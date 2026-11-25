# Write-ahead logging and undo/redo crash recovery

This node collects the model and correctness statement of write-ahead-logging recovery.

## Expansion

A sound expansion has separate pages for:

1. **Model.** Volatile buffer pages, stable database pages with page sequence numbers, and a stable log of
   update records (with before and after images), commit records and compensation records (CLRs) with
   undo-next links.
2. **Assumptions.** The write-ahead rule (a page is written to stable storage only after the log records of
   its updates are stable), force-log-at-commit, and an isolation discipline under which a loser's update is
   never overwritten by a committed transaction before the loser ends (for example strict two-phase
   locking).
3. **Recovery correctness.** Restart that redoes logged updates, including those of losers and compensation
   records, in log order when the page sequence number shows they are missing (repeating history), then undoes
   loser updates in reverse order while writing CLRs, restores a state reflecting exactly the committed
   transactions.
4. **Repeated crashes.** Recovery remains correct if crashes occur during restart, because page sequence numbers
   prevent redoing an update twice and CLRs and undo-next links prevent undoing an update twice. Without the
   isolation assumption, undoing an earlier loser can overwrite a later committed write.

## Depends on

- [Operation of a schedule](../conflict-serializability/op.md)

## Sources

- ARIES: A Transaction Recovery Method Supporting Fine-Granularity Locking and Partial Rollbacks Using Write-Ahead Logging (Mohan et al.), TODS 1992 — ACM TODS 17(1) 1992, abstract (p. 94): write-ahead logging, repeating history, a log sequence number in each page, logged rollbacks chained to forward records with bounded logging under repeated failures during restart. <https://cs.uwaterloo.ca/~david/cs448/aries-mohan.pdf>
- A. Silberschatz, H. F. Korth and S. Sudarshan, *Database System Concepts*, 7th edition, Chapter 19 slides 19.16 (no transaction modifies an item modified by an uncommitted one, ensured by strict two-phase locking), 19.19 (repeating history), 19.27–19.28 (redo and undo phases), 19.31 (commit after the commit record is stable; the write-ahead rule), 19.62 (page sequence numbers prevent repeated redo) and 19.63 (compensation records with an undo-next field). <https://www.db-book.com/slides-dir/PDF-dir/ch19.pdf>
