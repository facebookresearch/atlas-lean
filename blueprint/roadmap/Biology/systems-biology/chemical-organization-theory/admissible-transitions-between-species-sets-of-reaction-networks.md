# Admissible transitions between species sets of reaction networks

**Setting.** Let $(S,R)$ be a reaction network with species $s_1,\dots,s_n$ and stoichiometric matrix $N\in\mathbb{Z}^{n\times m}$. A flux $v\in\mathbb{R}^m_{\ge0}$ is *feasible* for a species set $A$ if it is supported on reactions all of whose reactants lie in $A$. A set $A$ is *closed* if every reaction whose reactants lie in $A$ produces only species of $A$, *self-maintaining* if some feasible flux with every such reaction active gives $(Nv)_i\ge0$ for all $s_i\in A$, and an *organization* if it is both. For a transition $T=(A,B)$ between species sets, let $\delta(T)=\vec B-\vec A\in\{-1,0,1\}^n$ be the difference of indicator vectors and $J(T)$ the indices of species not in $A\cap B$. $T$ is *feasibly elementary admissible* if some flux $\hat v$ feasible for $A$ satisfies $\operatorname{sign}((N\hat v)_i) = \delta(T)_i$ for all $i\in J(T)$, and *feasibly admissible* if it is a finite composition of such elementary transitions (dropping feasibility gives *stoichiometric* admissibility).

**Theorem.**

1. (*Persistence.*) For any solution $c(t)$ of a kinetic system on $(S,R)$, the set of species that persist ($\liminf_t c_i(t)>0$) is an organization.
2. (*Composition.*) If $A\to B$ and $B\to C$ are feasibly admissible, so is $A\to C$; likewise for stoichiometric admissibility.
3. (*Structural transitions.*) An organization admits a feasibly admissible zero transition $A\to A$; a non-closed set admits a feasibly admissible transition adding species, and every step $A\to\mathrm{clos}_1(A)\to\cdots\to\mathrm{clos}(A)$ of building the closure is feasibly admissible.
4. (*Dynamics.*) For a solution of the mass-action ODE with initial presence set $S_0=\{s_i: c_i(0)>0\}$, the closure-building transition $S_0\to\mathrm{clos}(S_0)$ is feasibly admissible; under further conditions on the presence sets at later times, the observed transitions between them are feasibly admissible as well.

## Expansion

A species absent from $A$ can appear only if some reaction fed by $A$ produces it, which is the sign condition with $+1$; a present species can disappear only if a feasible flux consumes it net, giving $-1$. Under mass action every reaction whose reactants are present fires instantly, so species in the closure of the initial set appear immediately, in closure steps. Persistent species must be closed (otherwise products would appear and persist) and self-maintaining (a time average of the flux witnesses nonnegative net production), which makes them an organization.

## Sources

- S. Peter, B. Ibrahim, "A structural theory of admissible transitions in biological reaction networks", arXiv:2608.27201, Theorem 2.3, Propositions 3.12–3.14 and Theorem 3.15. <https://doi.org/10.48550/arXiv.2608.27201>
