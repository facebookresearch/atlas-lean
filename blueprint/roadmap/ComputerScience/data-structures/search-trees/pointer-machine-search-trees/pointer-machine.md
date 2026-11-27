# Pointer machine

A *pointer machine* operates on a memory of records, each with a fixed number of named pointer fields and scalar fields, together with a finite set of pointer registers and scalar registers. Its instructions load a field of the record designated by a pointer register into a register, store a register into such a field, allocate a fresh record, copy registers, test a pointer for null or two pointers for equality, apply a primitive scalar predicate or operation (such as comparison of keys), jump, and halt. There is no address arithmetic: records are reached only by following pointers. Each instruction costs one unit.

## Sources

- R. E. Tarjan, "A Class of Algorithms Which Require Nonlinear Time to Maintain Disjoint Sets", Journal of Computer and System Sciences 18(2), 1979.
- D. E. Knuth, "The Art of Computer Programming, Volume 1: Fundamental Algorithms", 3rd edition, Addison-Wesley, 1997.
