# Complexity of direct transmission inference

Let $T$ be a timed phylogeny: a rooted tree with time-stamps $\tau : V(T) \to \mathbb{R}_{\ge 0}$ satisfying $\tau(u) \le \tau(v)$ whenever $u$ is ancestral to $v$. Let $\Sigma$ be a finite set of hosts, $\hat\ell : L(T) \to \Sigma$ a leaf labelling (the host each sampled strain came from), $C$ a directed contact map on $\Sigma$, and $[\tau_e(s), \tau_r(s)]$ the entry and removal times of host $s$. A vertex labelling $\ell : V(T) \to \Sigma$ extending $\hat\ell$ makes an edge $(u,v)$ a *transmission edge* when $\ell(u) \ne \ell(v)$. It satisfies the **direct transmission constraint** when

1. no transmission edge enters the root host $\ell(r(T))$;
2. any two transmission edges $(u,v)$, $(u',v')$ with $\ell(v) = \ell(v')$ have $\ell(u) = \ell(u')$ (a unique infector per host);
3. any two transmission edges between the same ordered pair of hosts have overlapping time intervals, $[\tau(u),\tau(v)] \cap [\tau(u'),\tau(v')] \ne \emptyset$.

Several transmission edges between the same pair of hosts are allowed (a *weak bottleneck*). The induced transmission tree $S$ has vertex set $\Sigma$, an edge $(s,t)$ whenever some transmission edge goes from $s$ to $t$, and weight $w(s,t)$ equal to the number of such edges.

**Direct transmission inference (DTI).** Given $(T, \tau, \hat\ell, C, \tau_e, \tau_r)$, decide whether there is a vertex labelling $\ell$ satisfying the direct transmission constraint whose transmission tree $S$ is a spanning arborescence of $C$ and with $\tau(u) \in [\tau_e(s), \tau_r(s)]$ whenever $\ell(u) = s$. The counting version #DTI asks for the number of such labellings.

**Theorem.**
1. DTI is NP-complete.
2. #DTI is #P-complete.
3. Consequently #DTI has no fully polynomial randomized approximation scheme unless $\mathrm{NP} = \mathrm{RP}$.

By contrast, under a strong bottleneck ($w \equiv 1$) the solutions can be counted and sampled uniformly in polynomial time, and dropping the direct transmission constraint (keeping only the timing and contact constraints) also gives a polynomial dynamic program. The three solution sets are nested: $\mathcal L_{SB} \subseteq \mathcal L \subseteq \mathcal L_{REL}$.

## Proof depends on

- [1-IN-3-SAT is NP-complete](../../../../TheoryOfComputation/np-completeness/satisfiability/1-in-3-sat/one-in-three-sat-np-complete.md)

## Expansion

Membership in NP is immediate: a labelling is checked edge by edge. Hardness comes from a reduction from 1-in-3SAT, in which each clause becomes a gadget of hosts and subtrees whose admissible labellings choose exactly one true literal; the unique-infector and overlapping-interval conditions are what couple the gadgets. The reduction is parsimonious, preserving the number of solutions, so the #P-completeness of #1-in-3SAT transfers to #DTI. Since even deciding non-emptiness is NP-hard, a relative-error approximation of the count in randomized polynomial time would decide DTI in RP. In practice the problem is encoded as a Boolean formula and handed to approximate model counters and near-uniform samplers; alternatively one samples uniformly from the polynomially countable relaxed set $\mathcal L_{REL}$ and rejects labellings that violate the direct transmission constraint, which is uniform on $\mathcal L$ but can be slow when $|\mathcal L| \ll |\mathcal L_{REL}|$.

## Sources

- P. Sashittal, M. El-Kebir, "Sampling and summarizing transmission trees with multi-strain infections", Bioinformatics 36 (Suppl. 1) (2020) i362–i370, Definitions 1–4, Problems 1–2, Section 3.1, Theorems 1–2, <https://doi.org/10.1093/bioinformatics/btaa438>, PMCID PMC7355255.
