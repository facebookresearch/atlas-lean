# Somewhere statistical soundness of arguments

An argument system with a common reference string is *somewhere statistically sound* if its reference string can be generated in a mode that depends on a hidden index or hidden query pattern $i^{*}$, such that (i) for every two choices of $i^{*}$ the reference strings are computationally indistinguishable, and (ii) in the mode with index $i^{*}$, for every statement that is false at the location $i^{*}$ (for example, an incorrect computation step or a false batch instance), no accepting proof exists, even for unbounded provers, except with negligible probability over the generation. Somewhere statistical soundness allows soundness arguments that guess the location of cheating and then argue information-theoretically, which is also what makes such arguments post-quantum when the indistinguishability is.

## Depends on

- [Non-interactive batch arguments for NP](batch-argument.md)

## Sources

- Yael Tauman Kalai, Vinod Vaikuntanathan, Rachel Yun Zhang, "Somewhere Statistical Soundness, Post-Quantum Security, and SNARGs", TCC (2021).
- Yael Tauman Kalai, Omer Paneth, Lisa Yang, "How to Delegate Computations Publicly", STOC (2019), IACR ePrint 2018/776.
