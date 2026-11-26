# IEEE status flags

The five exception flags of IEEE 754 an operation can raise: invalid
operation, division by zero, overflow, underflow and inexact. Each operation returns the flags it
raises; IEEE's status flags are sticky, so a computation accumulates them by disjunction.

## Sources

- IEEE Std 754-2019, Clause 7; Goldberg, *What every computer scientist should know about floating-point arithmetic*, ACM Computing Surveys 23(1), 1991, Section 2.3.
