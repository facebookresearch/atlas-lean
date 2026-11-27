# Banker's algorithm

## The system

- [Claims and allocations of processes](system.md)

## Safety and the banker's algorithm

- [Remaining need](need.md)
- [To Detection State](to-detection-state.md)
- [Safe sequence](safe-seq.md)
- [Safe Seq iff reduces](safe-seq-iff-reduces.md)
- [Safe state](safe.md)
- [Safe sequences are monotone in the free resources](mono.md)
- [Removing a process from a safe sequence](erase.md)
- [A safe state is not deadlocked](exists-runnable.md)
- [Letting a process that fits finish preserves safety](safe-iff-safe-erase.md)
- [Safe iff detect eq nil](safe-iff-detect-eq-nil.md)
- [Banker's safety algorithm with fuel](safety-check-aux.md)
- [The safety loop agrees with deadlock detection](safety-check-aux-iff-reduce-aux.md)
- [Banker's safety algorithm](safety-check.md)
- [Correctness of the safety algorithm](safety-check-iff.md)
- [Granting a request](grant.md)
- [Remaining need after a grant](need-grant-self.md)
- [Resource-request algorithm](request.md)
- [The request algorithm grants exactly the safe requests within the claim and the free resources](request-eq-some-iff.md)
- [Granted requests lead to safe states](request-safe.md)
- [Safety Check eq true iff detect eq nil](safety-check-eq-true-iff-detect-eq-nil.md)
