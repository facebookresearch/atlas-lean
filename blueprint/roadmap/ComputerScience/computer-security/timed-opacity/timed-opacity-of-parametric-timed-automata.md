# Timed opacity of parametric timed automata

A timed automaton is opaque with respect to a private location on the way to a final location if an attacker who measures the time to reach the final location cannot tell whether the private location was visited. The parametric versions ask for parameter valuations that make the automaton opaque.

**Parametric timed automata.** Clocks $\mathbb{X} = \{x_1, \dots, x_H\}$ take values in $\mathbb{R}_{\ge 0}$ and parameters $\mathbb{P} = \{p_1, \dots, p_M\}$ take values in $\mathbb{Q}_{\ge 0}$. A guard is a conjunction of constraints $x \bowtie \sum_{i} \alpha_i p_i + d$ with ${\bowtie} \in \{<, \le, =, \ge, >\}$ and $\alpha_i, d \in \mathbb{Z}$. A parametric timed automaton (PTA) is $\mathcal{A} = (\Sigma, L, \ell_0, \ell_f, \mathbb{X}, \mathbb{P}, I, E)$ with a finite set of actions $\Sigma$, a finite set of locations $L$, an initial location $\ell_0$, a final location $\ell_f$, an invariant guard $I(\ell)$ for each location, and finitely many edges $(\ell, g, a, R, \ell')$ with a guard $g$, an action $a$ and a set $R \subseteq \mathbb{X}$ of clocks to reset. A parameter valuation $v$ gives a timed automaton $v(\mathcal{A})$, whose runs alternate delays, during which invariants must hold, and edges whose guard holds; a run starts in $\ell_0$ with all clocks $0$, and its duration is the sum of its delays. An L/U-PTA is a PTA whose parameters are partitioned into lower-bound and upper-bound parameters, each upper-bound parameter occurring only with nonnegative coefficients in constraints $x \le \cdots$, $x < \cdots$ and nonpositive ones in $x \ge \cdots$, $x > \cdots$, and the reverse for lower-bound parameters.

**Durations.** For locations $\ell, \ell'$, $\ell$ is reached on the way to $\ell'$ in a run $(\ell_0, \nu_0), \dots, (\ell_n, \nu_n)$ if $\ell_m = \ell$ and $\ell_n = \ell'$ for some $m \le n$ with $\ell_i \ne \ell'$ for all $i < m$; it is avoided on the way to $\ell'$ if $\ell_n = \ell'$ and $\ell_i \ne \ell$ for all $i \le n$. $\mathit{DReach}^{\ell}(v(\mathcal{A}), \ell')$ is the set of durations of runs of $v(\mathcal{A})$ in which $\ell$ is reached on the way to $\ell'$, and $\mathit{DReach}^{\neg\ell}(v(\mathcal{A}), \ell')$ the set of durations of runs in which it is avoided.

**Opacity.** For a private location $\ell_{priv}$, a target location $\ell_f$ and a set $D$ of durations, $v(\mathcal{A})$ is opaque with respect to $\ell_{priv}$ on the way to $\ell_f$ for execution times $D$ if $D \subseteq \mathit{DReach}^{\ell_{priv}}(v(\mathcal{A}), \ell_f) \cap \mathit{DReach}^{\neg\ell_{priv}}(v(\mathcal{A}), \ell_f)$, and fully opaque if $\mathit{DReach}^{\ell_{priv}}(v(\mathcal{A}), \ell_f) = \mathit{DReach}^{\neg\ell_{priv}}(v(\mathcal{A}), \ell_f)$. In particular $v(\mathcal{A})$ is fully opaque when no run reaches $\ell_f$ (both sets empty), while opacity for a nonempty set of execution times needs some duration realized both with and without $\ell_{priv}$. Instances are finite: guards carry integer coefficients and constants, and parameters range over $\mathbb{Q}_{\ge 0}$.

**Emptiness problems.** Given a PTA $\mathcal{A}$, $\ell_{priv}$ and $\ell_f$: timed opacity emptiness asks whether the set of valuations $v$ for which $v(\mathcal{A})$ is opaque for some nonempty set of execution times is empty; full timed opacity emptiness asks whether the set of valuations $v$ for which $v(\mathcal{A})$ is fully opaque is empty.

## Depends on

None.

## Proof depends on

None.

## Expansion

The attacker knows the model and observes only the time from the start to the final location. For timed automata, without parameters, the set of opaque execution times is computable and full timed opacity is decidable, using region-based computation of the two duration sets; for L/U-PTAs timed opacity emptiness is decidable, while full timed opacity emptiness is not.

## Sources

- Étienne André, Didier Lime, Dylan Marinho and Jun Sun, "Guaranteeing timed opacity using parametric timed model checking", *ACM Transactions on Software Engineering and Methodology* 31(4), 36 pages, 2022, <https://doi.org/10.1145/3502851>; read as arXiv:2206.05438v1, <https://arxiv.org/abs/2206.05438v1>: Section 3 (clocks, parameters, guards, Definitions 1 and 2 of PTAs and L/U-PTAs, runs, durations, reaching and avoiding a location on the way to another) and Section 4 (Definitions 9 and 10 of timed opacity and full timed opacity, and the decision problems), with the emptiness problems stated in Sections 6 and 7.
