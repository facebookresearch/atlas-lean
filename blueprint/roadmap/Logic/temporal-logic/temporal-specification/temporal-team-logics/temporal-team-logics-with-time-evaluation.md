# Temporal team logics with time evaluation functions

TeamLTL, TeamCTL and TeamCTL* evaluate temporal formulas on multisets of traces (teams) whose positions advance asynchronously, as dictated by a time evaluation function; the CTL-style quantifiers range over time evaluation functions instead of paths.

**Definition.** Traces are infinite sequences $t \in (2^{AP})^\omega$. For a multiset $T$ of traces, a *stuttering time evaluation function* (tef) is a map $\tau : \mathbb N \times T \to \mathbb N$, giving the local position of each trace at each global time, that is *monotone* ($\tau(i, t) \le \tau(i+1, t)$) and *stepwise* ($\tau(i+1, t) \le \tau(i, t) + 1$); a *tef* is moreover *strictly monotone* (at every step some trace advances), and it is *initial* if $\tau(0, t) = 0$ for all $t$. The formulas of *TeamLTL* are those of LTL in negation normal form,

$$
\varphi ::= p \mid \neg p \mid \varphi \wedge \varphi \mid \varphi \vee \varphi \mid \mathsf X\varphi \mid \varphi\,\mathsf U\,\varphi \mid \varphi\,\mathsf W\,\varphi,
$$

evaluated on $(T, \tau, i)$ for a *stuttering temporal team* $(T, \tau)$, that is, with $\tau$ a stuttering tef for $T$ (Definitions 3.1 and 3.2): $p$ holds iff $p \in t[\tau(i, t)]$ for every $t \in T$, and $\neg p$ iff $p \notin t[\tau(i, t)]$ for every $t \in T$; $\wedge$ is conjunction; $\varphi \vee \psi$ holds iff $T$ splits as a disjoint union $T_1 \uplus T_2$ with $(T_1, \tau, i) \models \varphi$ and $(T_2, \tau, i) \models \psi$, where $\tau$ is restricted to $T_1$ and to $T_2$ (such a restriction may stutter even when $\tau$ is strictly monotone, which is why the semantics is defined on stuttering temporal teams); $\mathsf X\varphi$ holds iff $(T, \tau, i+1) \models \varphi$, and $\mathsf U$, $\mathsf W$ are evaluated along the global time $i$ as in LTL. *TeamCTL* adds the quantifiers $\exists$ and $\forall$ in front of temporal operators: $(T, \tau, i) \models \exists\varphi$ iff $(T, \tau', i) \models \varphi$ for some tef $\tau'$ of $T$ agreeing with $\tau$ up to time $i$, and dually for $\forall$; *$\exists$TeamCTL* is the fragment without the universally quantified modalities. *TeamCTL\** takes its syntax from CTL\*, with the same quantifiers $\exists$ and $\forall$ over tefs in place of path quantifiers, and *$\exists$TeamCTL\** is its fragment without $\forall$ (Section 3.2). The *Boolean disjunction* $\varphi \mathbin{\varovee} \psi$ holds iff $\varphi$ holds or $\psi$ holds on the same team, and TeamCTL$(\varovee)$ adds it. $T \models_\exists \varphi$ means $(T, \tau, 0) \models \varphi$ for some initial tef $\tau$. The *model-checking problem* asks, given a formula $\varphi$ and a finite Kripke structure $\mathcal K$, whether $\mathrm{Traces}(\mathcal K) \models_\exists \varphi$.

## Depends on

- [Formulas of linear temporal logic](../../linear-temporal-logic/formula.md)
- [Hyperproperties, hypersafety and k-safety](../hyperproperties-hypersafety-and-k-safety.md)
- [CTL formulas](../../computation-tree-logic/formula.md)

## Proof depends on

None.

## Expansion

Teams describe sets of traces directly, so these logics express hyperproperties without trace quantifiers. With the unique initial *synchronous* tef, in which all traces advance in lockstep, TeamLTL is the synchronous team semantics of Krebs, Meier, Virtema and Zimmermann; on singleton teams it coincides with LTL. Further atoms, such as dependence atoms $\mathrm{dep}(\varphi_1, \ldots, \varphi_n, \psi)$ and inclusion atoms $\varphi_1 \ldots \varphi_n \subseteq \psi_1 \ldots \psi_n$ with propositional arguments, extend the logics.

## Sources

- J. O. Gutsfeld, A. Meier, C. Ohrem and J. Virtema, "Temporal Team Semantics Revisited", in *Proceedings of the 37th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2022)*, ACM, 2022, pp. 1–13, <https://doi.org/10.1145/3531130.3533360>; journal version *Journal of Computer and System Sciences* 163, 2027, article 103859, <https://doi.org/10.1016/j.jcss.2026.103859>; numbers from arXiv:2110.12699v3, <https://arxiv.org/abs/2110.12699v3>: Section 3.1 (Definitions 3.1 and 3.2, properties of tefs), Section 3.2 (TeamLTL, TeamCTL, TeamCTL*, the satisfaction modes and decision problems) and Section 3.3 (extensions by atoms and Boolean disjunction).
