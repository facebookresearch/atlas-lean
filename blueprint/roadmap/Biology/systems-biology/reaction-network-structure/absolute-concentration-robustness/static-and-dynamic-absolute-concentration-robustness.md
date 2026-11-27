# Static and dynamic absolute concentration robustness

**Setting.** Let $\dot x=f(x)$ be a smooth dynamical system on $\mathbb{R}^n_{\ge0}$, with the orthant forward invariant; mass-action reaction networks are the main example. The *kinetic subspace* is $\mathrm{span}(\mathrm{Im}\,f)$. Two points $x,y$ are *compatible* if $y-x$ lies in this subspace, and two sets are compatible if some pair of their points is.

**Definitions.**

- **Static ACR** (Shinar–Feinberg). The system has a positive steady state, and for some species index $i$ and value $a_i^*>0$, every positive steady state lies in the hyperplane $\{x_i=a_i^*\}$.
- **Dynamic ACR.** For some $i$ with $f_i\not\equiv0$ and some $a_i^*>0$, every positive initial condition compatible with $\{x\in\mathbb{R}^n_{>0}:x_i=a_i^*\}$ has a unique solution on a maximal interval $[0,T_0)$, and $x_i(t)\to a_i^*$ as $t\to T_0$.
- **Basin types.** Let $N_{i,a_i^*}$ be the set of $i$-th coordinates of positive points that are *not* compatible with $\{x_i=a_i^*\}$. A dynamic ACR variable is *full basin* if $N_{i,a_i^*}=\varnothing$, *wide basin* if $N_{i,a_i^*}$ is bounded above, and *narrow basin* otherwise.

**Theorem.**

1. Each static or dynamic ACR variable has a unique ACR value.
2. The system has a unique positive steady state iff every variable is a static ACR variable.
3. A globally attracting positive steady state makes every variable a full basin dynamic ACR variable. Conversely, if every variable is dynamic ACR, the system has a globally attracting positive steady state, so every variable is full basin dynamic ACR.
4. Let $x_i$ be dynamic ACR with value $a_i^*$, and let $\mathcal{B}$ be the set of positive steady states. Then $x_i$ is static ACR with value $a_i^*$ iff $\varnothing\ne\mathcal{B}$ and every point of $\mathcal{B}$ is compatible with $\{x_i=a_i^*\}$.

Static ACR is neither necessary nor sufficient for the long-run, initial-condition-independent robustness that experiments measure. Two one-species networks show this. In $2A\to3A$, $A\to0$, the unique steady state $a=k/k'$ is static ACR but repelling, so the system is not dynamic ACR. In $0\rightleftharpoons A$, the steady state is globally attracting, so the system is both static and full basin dynamic ACR.

## Expansion

Uniqueness of the dynamic ACR value follows by contradiction. If $x_i$ had two values, the hyperplane $\{x_i=a_i^*\}$ would be compatible with no other level set $\{x_i=c\}$. Its compatible region would then lie inside the hyperplane, which forces $f_i\equiv0$. For the converse in item 3: since $f_i\not\equiv0$ for every $i$, the kinetic subspace is transversal to each hyperplane. So there is a neighborhood of $a^*=(a_1^*,\dots,a_n^*)$ compatible with all of them, and trajectories starting there converge to $a^*$. If the kinetic subspace were a proper subspace, some invariant compatibility class would meet this neighborhood without containing $a^*$, a contradiction. Hence the kinetic subspace is $\mathbb{R}^n$ and $a^*$ attracts globally. In item 4, a positive steady state compatible with the hyperplane is a constant trajectory that must converge to $a_i^*$, so its $i$-th coordinate is $a_i^*$. Dynamic ACR thus refines static ACR into a statement about global dynamics. The Shinar–Feinberg deficiency-one criterion gives static ACR only.

## Sources

- Badal Joshi and Gheorghe Craciun, "Foundations of static and dynamic absolute concentration robustness", Journal of Mathematical Biology 85 (2022), 53, <https://doi.org/10.1007/s00285-022-01823-2>; numbering as in arXiv:2104.14070: Definitions 2.1, 2.2, 2.3 and 2.5, Theorem 2.4, Theorem 2.6, Corollary 2.7, Theorem 2.8, and the one-species examples of Section 4.
