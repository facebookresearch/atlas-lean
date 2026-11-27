# Concurrency control and recovery

Recoverability classes of transaction histories, timestamp ordering and multiversion concurrency control, multiversion histories and one-copy serializability, snapshot isolation and its dangerous structures, liveness of the wait-die and wound-wait schemes, and write-ahead logging with undo/redo recovery. Conflict serializability and two-phase locking have folders of their own.

- [Recoverable, cascadeless and strict schedules](recoverable-cascadeless-and-strict-schedules.md)
- [Timestamp ordering and multiversion concurrency control](timestamp-ordering-and-multiversion-concurrency-control.md)
- [Multiversion histories and one-copy serializability](remaining-clauses-of-multiversion-histories-and-one-copy-ser.md)
- [One-copy serializability of finite histories is decidable](one-copy-serializability-of-finite-histories-is-decidable.md)
- [Snapshot isolation and the write-skew anomaly](snapshot-isolation-and-the-write-skew-anomaly.md)
- [Dangerous structures in non-serializable SI histories](dangerous-structures-characterize-si-non-serializability.md)
- [No starvation under wait-die/wound-wait with retained timestamps (optional liveness)](no-starvation-under-wait-die-wound-wait-with-retained-timest.md)
- [Starvation under wait-die without its liveness assumptions](starvation-under-wait-die-without-its-liveness-assumptions.md)
- [Write-ahead logging and undo/redo crash recovery](write-ahead-logging-and-undo-redo-crash-recovery.md)
