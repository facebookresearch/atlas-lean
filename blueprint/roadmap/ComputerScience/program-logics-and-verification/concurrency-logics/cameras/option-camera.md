# Option camera

The *option camera* $M^?$ over a camera $M$ is defined by adding a unit element $\bot$: composition with $\bot$ returns the other argument, and the core is made total.

For a camera $M$, $M^? = M \uplus \{\bot\}$ with $\bot$ $n$-equal only to itself, composition extended by $a^? \cdot \bot = \bot \cdot a^? = a^?$, $\bot$ valid at every index (the evident lifting for a unit, which the documentation leaves implicit) and $\mathcal{V}(a)$ as in $M$ for $a \in M$, and core $|\bot| \triangleq \bot$ and $|a| \triangleq |a|_M$ for $a \in M$, read in $M^?$. With these operations $M^?$ is a unital camera with unit $\bot$ and total core.

## Depends on

- [Cameras](cameras.md)

## Proof depends on

- [Cameras](cameras.md)

## Expansion

The camera axioms for elements of $M$ are those of $M$, and $\bot$ is a unit with $|\bot| = \bot$; the core is total because a missing core of $M$ becomes the element $\bot$ of $M^?$. The source's authoritative construction uses $\mathrm{EX}(M)^?$.

## Sources

- Iris Team, "The Iris 3.1 documentation", technical documentation (not peer reviewed) that the JFP article cites as its appendix (Iris Team, 2017), version of April 29, 2019, <https://plv.mpi-sws.org/iris/appendix-3.1.pdf>, Section 4.3 (option camera with its core), supplementary documentation.
- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Figure 9 (lifting of composition to M?) and Section 6.3.3 (use of the option in AUTH).
