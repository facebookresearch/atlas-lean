# Word-RAM implementation certificate with potential-amortized running time

Fix a word size $w$, a specification $D$ and an abstract initial state $s_0$. A *Word-RAM implementation* of $D$ from $s_0$ is a fixed program with $r$ registers together with a contiguous memory block $[b, b + \mathsf{space})$, a representation relation $\mathsf{rep}(s, x)$ between abstract states and machine states, an initial machine state $x_0$ with $\mathsf{rep}(s_0, x_0)$, a potential $\Phi(x) \ge 0$ and a charge function $c(s, o)$, such that from every represented state and admissible operation $o$ (arguments placed in designated input registers), the program halts within $c(s,o) + \Phi(x) - \Phi(x')$ instructions in a machine state $x'$ representing some $(s', a) \in \mathsf{step}(s, o)$, reading and writing only inside its block and its own registers.

The *persistent registers* are the non-input registers whose contents survive between operations. A *randomized* certificate additionally allows `rand` instructions and a seed $\theta$ drawn from a law $\nu$; the bound is then on expected instructions against oblivious operation sequences, with $x_0$, $\mathsf{rep}$ and $\Phi$ depending on $\theta$ and $\mathsf{rep}_\theta(s_0, x_0(\theta))$ for every seed $\theta$. A *with-high-probability* certificate instead bounds every operation by a fixed worst-case instruction budget except on an event of probability at most $\delta$.

## Depends on

- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)
- [Randomized word RAM](../../sorting-and-searching/word-ram-integer-algorithms/randomized-word-ram.md)
- [State-transition specification of a data structure](state-transition-specification.md)
- [Oblivious-sequence specification of a randomized data structure](oblivious-sequence-specification.md)
- [Amortized cost of an operation](../amortized-analysis/amortized-cost.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- M. Mitzenmacher and E. Upfal, "Probability and Computing", 2nd edition, Cambridge University Press, 2017.
- M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, "Modern Hashing Made Simple", Proceedings of the 2024 SIAM Symposium on Simplicity in Algorithms (SOSA), 2024.
