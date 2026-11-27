# Incidence matrix and marking equation of an ordinary net

Let $N$ be an ordinary [Petri net](../place-transition-petri-nets.md) with places $P$ and transitions $T$. Its *incidence matrix* $\mathbf{N} : P \times T \to \{-1, 0, 1\}$ has $\mathbf{N}(s, t) = -1$ if $s$ is an input but not an output place of $t$, $1$ if $s$ is an output but not an input place of $t$, and $0$ otherwise. The *Parikh vector* $\vec\sigma : T \to \mathbb{N}$ of a finite sequence $\sigma$ of transitions counts the occurrences of each transition. **Marking equation lemma:** if $M [\sigma\rangle M'$, then $M' = M + \mathbf{N} \cdot \vec\sigma$. For a pure net this is [the state equation of a Petri net](../state-equation.md).

## Depends on

- [Place/transition Petri nets](../place-transition-petri-nets.md)
- [The state equation of a Petri net](../state-equation.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Definitions 4.2.1 and 4.2.3 and Lemma 4.2.4 ("Marking Equation Lemma") with its proof, p. 82.
