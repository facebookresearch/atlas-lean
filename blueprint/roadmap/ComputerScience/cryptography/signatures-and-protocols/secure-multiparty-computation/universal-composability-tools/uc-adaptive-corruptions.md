# Adaptive corruptions in UC execution

In UC execution with *adaptive corruptions*, the adversary may at any time issue $(\mathrm{corrupt}, i)$ for a party $i$; it then learns a *snapshot* of the party's memory, which is the full history of its inputs, coins and messages in the *non-erasing* model, or only its current state in the *erasing* model, and controls the party from then on. Emulation against adaptive adversaries requires a simulator that, upon each corruption in the ideal world, produces a consistent snapshot from the party's ideal inputs and outputs. A *static* adversary corrupts only an initial set fixed before the execution. The adaptive distinguishing advantage is symmetric and satisfies the triangle inequality, and polynomially call-bounded environments and adversaries remain so under these operations.

## Depends on

- [UC emulation](../uc-emulation.md)
- [Interactive machines, linking and the single-token execution model](uc-interactive-machines.md)

## Sources

- Ran Canetti, "Universally Composable Security", Journal of the ACM, 2020.
