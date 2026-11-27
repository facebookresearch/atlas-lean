# Kripke structures with initial states

A *Kripke structure* over a set $AP$ of atomic propositions is a tuple $M = (S, I, T, L)$ of a set $S$ of states (finite in the source), a set $I \subseteq S$ of initial states, a transition relation $T \subseteq S \times S$ and a labelling $L : S \to \mathcal{P}(AP)$. It is *finite* if $S$ is finite and *total* if every state has a successor: for each $s$ there is $t$ with $(s, t) \in T$. A *path* is a sequence $s_0, s_1, \dots$ with $(s_i, s_{i+1}) \in T$ for all $i$, and an *initialized* path is one with $s_0 \in I$. For symbolic algorithms one takes $S = \{0, 1\}^n$, so that $I$, $T$ and each proposition $p$ are given by propositional formulas $f_I(s)$, $f_T(s, t)$ and $f_p(s)$ over the state variables.

## Sources

- A. Biere, A. Cimatti, E. Clarke and Y. Zhu, "Symbolic model checking without BDDs", *TACAS 1999*, LNCS 1579, Springer, 1999, <https://fmv.jku.at/papers/BiereCimattiClarkeZhu-TACAS99.pdf>, Section 2, Definition 1 and the Boolean encoding after it.
