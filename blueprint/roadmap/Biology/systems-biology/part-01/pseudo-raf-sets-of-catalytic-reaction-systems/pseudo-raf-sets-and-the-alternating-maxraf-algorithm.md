# Pseudo-RAF sets and the alternating maxRAF algorithm

**Setting.** A catalytic reaction system (CRS) is $Q = (X, \mathcal R, C, F)$: a finite set $X$ of molecule types, a finite set $\mathcal R$ of reactions, a catalysis relation $C \subseteq X \times \mathcal R$ and a food set $F \subseteq X$. For $r \in \mathcal R$ let $\rho(r)$ and $\pi(r)$ be its reactants and products, and for $\mathcal R' \subseteq \mathcal R$ let $\pi(\mathcal R') = \bigcup_{r \in \mathcal R'} \pi(r)$. The **closure** $\mathrm{cl}_{\mathcal R'}(F)$ is the smallest set containing $F$ that contains $\pi(r)$ whenever it contains $\rho(r)$, for $r \in \mathcal R'$.

- A nonempty $\mathcal R' \subseteq \mathcal R$ is an **RAF** if every $r \in \mathcal R'$ has $\rho(r) \subseteq \mathrm{cl}_{\mathcal R'}(F)$ and some catalyst $x$ with $(x, r) \in C$ and $x \in \mathrm{cl}_{\mathcal R'}(F)$.
- $\mathcal R'$ is a **pseudo-RAF (pRAF)** if every $r \in \mathcal R'$ has $\rho(r) \subseteq F \cup \pi(\mathcal R')$ and some catalyst in $F \cup \pi(\mathcal R')$.
- $\mathcal R'$ is **$F$-generated** if $\mathrm{cl}_{\mathcal R'}(F) = F \cup \pi(\mathcal R')$.

Define $f, p : 2^{\mathcal R} \to 2^{\mathcal R}$ by

$$f(\mathcal R') = \{ r \in \mathcal R' : \exists (x,r) \in C,\ \rho(r) \cup \{x\} \subseteq \mathrm{cl}_{\mathcal R'}(F)\},\qquad p(\mathcal R') = \{ r \in \mathcal R' : \exists (x,r) \in C,\ \rho(r) \cup \{x\} \subseteq F \cup \pi(\mathcal R')\},$$

and let $\mathrm{fix}_p(\mathcal R')$ be the result of iterating $p$ from $\mathcal R'$ until a fixed point (possibly $\emptyset$).

**Lemma.** (i) The RAFs of $Q$ are exactly its $F$-generated pRAFs. (ii) A union of pRAFs is a pRAF; hence, if $Q$ has a pRAF, it has a unique maximum pRAF. (iii) $f$ and $p$ are monotone: $\mathcal R_1 \subseteq \mathcal R_2$ implies $f(\mathcal R_1) \subseteq f(\mathcal R_2)$ and $p(\mathcal R_1) \subseteq p(\mathcal R_2)$.

**Theorem (alternating algorithm).** Set $\mathcal R_0 = \mathcal R$ and, for $k \ge 0$, $\mathcal R_{k+1} = f(\mathrm{fix}_p(\mathcal R_k))$, stopping at the first $k$ with $f(\mathcal R_k) = \mathcal R_k$ or $\mathcal R_k = \emptyset$. The output is the maximum RAF (maxRAF) of $Q$ if $Q$ contains an RAF, and $\emptyset$ otherwise.

The maximum pRAF is the minimal model of a propositional Horn formula, so it can be computed in linear time by unit propagation; the closure computation in $f$ is the expensive step of the basic RAF algorithm (iterate $f$ alone), whose worst-case time is $O(|\mathcal R|^2 \log |\mathcal R|)$. Interleaving $\mathrm{fix}_p$ reduces the number of closure computations.

## Expansion

(i) An RAF satisfies the pRAF conditions because $\mathrm{cl}_{\mathcal R'}(F) \subseteq F \cup \pi(\mathcal R')$, and it is $F$-generated; conversely, for an $F$-generated pRAF the two reference sets coincide. (ii) Reactants and products of a union are unions, and $F \cup \pi(\mathcal R_i) \subseteq F \cup \pi(\bigcup_j \mathcal R_j)$. (iii) Closures and product sets grow with $\mathcal R'$. For the theorem, the maxRAF $\mathcal R_m$ is a fixed point of both $f$ and $p$, so by monotonicity $\mathcal R_m = p^n(\mathcal R_m) \subseteq p^n(\mathcal R_k)$ and $\mathcal R_m = f(\mathcal R_m) \subseteq f(\cdot)$ at every stage; thus $\mathcal R_m \subseteq \mathcal R_k$ for all $k$. The sequence decreases, so it stops; a nonempty set with $f(\mathcal R_k) = \mathcal R_k$ is an RAF containing $\mathcal R_m$, hence equals it. If there is no RAF, $f$ has no nonempty fixed point and the sequence ends at $\emptyset$.

## Sources

- W. Hordijk, J. I. Smith, M. Steel, "Algorithms for detecting and analysing autocatalytic sets", Algorithms for Molecular Biology (2015), section "Pseudo-RAFs and their use in a modified RAF algorithm" (Definition, Lemma 1, Lemma 2, Theorem 1) and Appendix (HORN-SAT formulation), <https://doi.org/10.1186/s13015-015-0042-8>, PMCID PMC4428007.
