# Crash atomicity of write-ahead data journaling

Consider a file system that applies each transaction, a set of new contents for some data and metadata blocks, with the [write-ahead data journaling](write-ahead-data-journaling.md) protocol. Single-sector writes are atomic, and the transaction-end (commit) block fits in one sector. The protocol runs in four steps:

1. **Journal write.** Write the transaction-begin block and the new block contents to the log, and wait for these writes to complete.
2. **Journal commit.** Write the commit block to the log, and wait for it to complete. The transaction is now committed.
3. **Checkpoint.** Write the new contents to their home locations.
4. **Free.** Only after all checkpoint writes are durable, mark the transaction free in the journal superblock.

Recovery scans the journal and redoes, in order, every committed transaction that has not been freed, writing its logged block contents to their home locations.

**Claim.** For every crash point, including crashes during recovery, the file-system state after recovery completes is either the state before the transaction or the state after it.

**Argument.**
- *Crash before the commit block is durable.* The transaction is not committed and recovery skips it. No home location has been written, because checkpointing starts only after step 2 completes. The state is the old one.
- *Crash after commit but before the transaction is freed.* Recovery rewrites all its logged blocks to their home locations, so the state is the new one. A home block already written by the checkpoint is written again with the same contents.
- *Crash after the transaction is freed.* By step 4 the checkpoint is durable, so the home locations already hold the new state.
- *Crash during recovery.* Redo writes full block images and does not depend on the current contents of home locations. Repeating it is therefore idempotent, and recovery may simply run again.

The waits are needed. If the disk may reorder the commit block ahead of the logged blocks, without a barrier or flush in between, recovery can replay a committed transaction whose logged contents are garbage.

## Depends on

- [Write-ahead data journaling](write-ahead-data-journaling.md)

## Background

- [The asynchronous disk model of Crash Hoare logic](the-asynchronous-disk-model-of-crash-hoare-logic.md)

## Sources

- R. H. Arpaci-Dusseau and A. C. Arpaci-Dusseau, *Operating Systems: Three Easy Pieces*, version 1.10, Chapter 42, "Crash Consistency: FSCK and Journaling", <https://pages.cs.wisc.edu/~remzi/OSTEP/file-journaling.pdf>: Section 42.3, the data journaling protocol with journal write, journal commit, checkpoint and free; recovery by redo logging; the safety of crashes during checkpointing; write barriers and the reordering hazard; and making the commit block a single 512-byte sector. The source argues informally; the case analysis above makes the argument explicit.
