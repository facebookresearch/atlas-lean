# Two-run product of IMP commands

Use the while-language [IMP](../../programming-language-semantics/operational-semantics-of-imp/cmd.md), whose variables are $x_i$ for $i \in \mathbb{N}$ and whose [states](../../programming-language-semantics/operational-semantics-of-imp/state.md) are functions $\sigma : \mathbb{N} \to \mathbb{N}$, with its [big-step semantics](../../programming-language-semantics/operational-semantics-of-imp/big-step.md) $\langle c, s \rangle \Downarrow t$. For an injective $\rho : \mathbb{N} \to \mathbb{N}$, let $c[\rho]$ rename every variable $x_i$ in $c$ to $x_{\rho(i)}$. Fix the two copies
- $c^{(0)} = c[i \mapsto 2i]$;
- $c^{(1)} = c[i \mapsto 2i + 1]$.

Pair states by $\langle s_0, s_1\rangle(2i) = s_0(i)$ and $\langle s_0, s_1\rangle(2i + 1) = s_1(i)$. Every state is a pair of exactly one pair of states.

**Theorem.**
1. **Renaming.** For injective $\rho$ and states $u, u'$: $\langle c[\rho], u \rangle \Downarrow u'$ if and only if both $\langle c, u \circ \rho \rangle \Downarrow u' \circ \rho$ and $u'$ agrees with $u$ outside the range of $\rho$.
2. **Two-run product.** For all states $s_0, s_1, t_0, t_1$: $\langle c, s_0 \rangle \Downarrow t_0$ and $\langle c, s_1 \rangle \Downarrow t_1$ hold if and only if $\langle c^{(0)} ; c^{(1)}, \langle s_0, s_1\rangle \rangle \Downarrow \langle t_0, t_1 \rangle$. Every terminating run of $c^{(0)} ; c^{(1)}$ from $\langle s_0, s_1\rangle$ ends in a state of this form.

The correspondence concerns pairs of terminating runs and their initial and final states only. It says nothing about divergence, timing or intermediate states.

**Proof.**
1. Induct on the big-step derivation. Expressions evaluate in $u$ after renaming exactly as in $u \circ \rho$ before renaming. An assignment to $x_{\rho(i)}$ changes only position $\rho(i)$. The cases for skip, sequencing, the conditional and the loop follow from the induction hypothesis.
2. By part 1 with $\rho(i) = 2i$, running $c^{(0)}$ from $\langle s_0, s_1\rangle$ terminates exactly in the states $\langle t_0, s_1\rangle$ with $\langle c, s_0\rangle \Downarrow t_0$, since the odd positions are untouched. Running $c^{(1)}$ from there terminates exactly in $\langle t_0, t_1\rangle$ with $\langle c, s_1\rangle \Downarrow t_1$. The sequencing rule composes the two runs.

## Depends on

- [Big-step semantics of IMP](../../programming-language-semantics/operational-semantics-of-imp/big-step.md)

## Sources

- M. R. Clarkson and F. B. Schneider, "Hyperproperties", *Journal of Computer Security* 18(6):1157–1210, 2010, <https://www.cs.cornell.edu/info/people/fbs/publications/Hyperproperties.pdf>, Section 4: the sequential self-composition $P ; P'$ of a program with a copy in which every variable is renamed to a fresh primed variable, used to verify secure information flow as a trace property of $P ; P'$ over terminating executions (after Barthe et al.). The renaming and frame lemmas for IMP are written out here.
