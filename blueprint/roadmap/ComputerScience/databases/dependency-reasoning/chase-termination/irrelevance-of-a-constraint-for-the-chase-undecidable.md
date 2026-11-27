# Irrelevance of a constraint for the chase is undecidable

A constraint is irrelevant for chasing a given instance if no chase sequence ever fires it; discarding irrelevant constraints could certify chase termination for that instance. Deciding whether a given tuple-generating dependency is irrelevant is undecidable.

**Setting (Meier, Schmidt and Lausen).** Constraints are tuple-generating dependencies (TGDs) and equality-generating dependencies (EGDs). The (standard) chase of an instance $I$ with a finite set $\Sigma$ of constraints repeatedly applies a step $I_j \xrightarrow{\alpha, \bar{a}} I_{j+1}$ that fires a constraint $\alpha \in \Sigma$ on a tuple $\bar{a}$ whose body matches but whose head is not yet satisfied, adding head atoms with fresh nulls (TGD) or equating terms (EGD). A constraint $\alpha \in \Sigma$ is *$(I, \Sigma)$-irrelevant* if there is no chase sequence $I \xrightarrow{\alpha_1, \bar{a}_1} \cdots$ starting from $I$ in which $\alpha$ eventually fires.

**Theorem (Meier, Schmidt and Lausen).** Given a set $\Sigma$ of constraints, a constraint $\alpha \in \Sigma$ and an instance $I$, it is undecidable whether $\alpha$ is $(I, \Sigma)$-irrelevant.

The paper's motivation is a data-dependent termination guarantee: if the constraints that remain after removing $(I, \Sigma)$-irrelevant ones lie in a level $T[k]$, $k \ge 2$, of its stratification-based termination hierarchy, the chase of $I$ with $\Sigma$ terminates. The theorem shows that the irrelevant constraints cannot be computed exactly, so the paper works with sufficient conditions.

## Depends on

- [Tuple- and equality-generating dependencies and the chase](../../dependencies-and-the-chase/tuple-and-equality-generating-dependencies-and-the-chase.md)

## Proof depends on

- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The reduction is from the problem whether a Turing machine started on the empty input ever uses a given transition $t$. Reusing a grid construction from earlier work on chase termination, the constraints $\Sigma_M$ describe the computation: relations $T(x, a, y)$ and $H(x, s, y)$ give tape and head edges labeled by symbols and states, $L$ and $R$ give vertical edges between successive configurations, a constraint creates the initial configuration and fires exactly once, TGDs for each transition $\delta$ build the next configuration and add a marker $A_\delta$, and copy rules propagate unchanged tape cells. Each transition $\delta$ is also represented by a single TGD $A_\delta(x) \to B_\delta(x)$, and $\alpha_t$ is the one for $t$. The chase builds a grid whose rows are the machine's configurations, so $\alpha_t$ can fire in some chase sequence exactly when $M$ reaches $t$.

## Sources

- Michael Meier, Michael Schmidt and Georg Lausen, "On chase termination beyond stratification", Proceedings of the VLDB Endowment 2(1), pp. 970–981, 2009, <https://doi.org/10.14778/1687627.1687737>; the definition of $(I, \Sigma)$-irrelevance and the undecidability theorem with its proof sketch in the subsection "Static Termination Guarantees" of the section "Data-dependent Termination" of arXiv:0906.4228v2, read at <https://arxiv.org/abs/0906.4228v2>.
