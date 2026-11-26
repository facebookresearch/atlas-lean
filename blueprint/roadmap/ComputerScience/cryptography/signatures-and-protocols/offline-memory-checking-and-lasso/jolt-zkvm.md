# Jolt: SNARKs for virtual machines where every instruction is a lookup

For a CPU instruction set (instantiated with RISC-V), let each instruction's input-output behavior on $W$-bit registers be the table of size $2^{2W}$ mapping operand pairs to results. Every such table for the base integer instruction set is decomposable in the sense used by Lasso. The Jolt SNARK proves correct execution of $T$ steps by (i) one Lasso lookup per step for instruction semantics, (ii) offline memory checking for registers and RAM, and (iii) a small R1CS for the fetch–decode logic, so that the prover per step commits to a constant number of small field elements and the overall prover cost is $O(T)$ group operations plus the commitment opening costs.

## Proof sketch

The decomposition lemma covers bitwise instructions; arithmetic and comparison instructions decompose via chunked carry-free or comparison-prefix formulas. Combining Lasso, memory checking and a constant-size per-step constraint system yields the claim, with soundness inherited from the components.

## Depends on

- [Lasso: lookup arguments into huge decomposable tables](lasso-lookup.md)
- [Decomposable lookup tables](decomposable-table.md)
- [Offline memory checking with timestamps](offline-memory-checking.md)

## Proof depends on

- [Bitwise instruction tables decompose into small chunk tables](bitwise-table-decomposition.md)
- [Multiset equality certifies read-correctness of memory](memory-checking-soundness.md)

## Sources

- Arasu Arun, Srinath Setty, Justin Thaler, "Jolt: SNARKs for Virtual Machines via Lookups", EUROCRYPT (2024), IACR ePrint 2023/1217.
