# Write-ahead data journaling

In write-ahead data journaling, a transaction that updates a set of blocks first writes to the journal a transaction-begin block, the new contents of the data and metadata blocks, and then a transaction-end (commit) block; only after the commit block is durable are the blocks written to their home locations (checkpointing), after which the journal space is freed. After a crash, recovery scans the journal and replays, in order, every transaction whose commit block is present, and ignores transactions without a commit block.

## Depends on

- [A crash model of disks with volatile caches](the-asynchronous-disk-model-of-crash-hoare-logic.md)

## Sources

- R. H. Arpaci-Dusseau and A. C. Arpaci-Dusseau, *Operating Systems: Three Easy Pieces*, Arpaci-Dusseau Books, 2018, <https://pages.cs.wisc.edu/~remzi/OSTEP/>
