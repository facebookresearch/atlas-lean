# Equational theories and convergent subterm theories

Let $\mathcal F$ be a signature. An *equational theory* $E$ is a set of equations $u = v$ between terms of $T(\mathcal F, \mathcal X, \mathcal N)$, and $=_E$ is the smallest
equivalence relation on terms that contains $u\theta =_E v\theta$ for every equation $u = v$ of $E$ and every substitution $\theta$ and is closed under the function symbols
($u_i =_E v_i$ for all $i$ implies $f(u_1, \dots, u_k) =_E f(v_1, \dots, v_k)$). An equational theory defined by a finite set of equations $\{M_i = N_i\}_{i=1}^n$ with no free
names is a *convergent subterm theory* if the rewriting system $\{M_i \to N_i\}_{i=1}^n$ is convergent and each $N_i$ is a proper subterm of $M_i$ or a constant; then
$U =_E V$ if and only if $U$ and $V$ have the same normal form. Examples are the destructor equations $\mathrm{fst}(\langle x, y\rangle) = x$,
$\mathrm{snd}(\langle x, y\rangle) = y$ and $\mathrm{dec}(\mathrm{enc}(x, y), y) = x$.

## Sources

- V. Cortier and S. Kremer, "Formal models and techniques for analyzing security protocols: a tutorial", *Foundations and Trends in Programming Languages* 1(3), 2014, doi:10.1561/2500000001, copy at <https://inria.hal.science/hal-01090874>: Section 4.1.1 (equational theories).
- M. Abadi and V. Cortier, "Deciding knowledge in security protocols under equational theories", *Theoretical Computer Science* 367(1–2), 2006; preprint of 18 October 2005 at <https://members.loria.fr/VCortier/files/Papers/AbadiCortierTCS06.pdf>: Section 4.1, Definition 1 (convergent subterm theories), and Section 4.2 (examples).
