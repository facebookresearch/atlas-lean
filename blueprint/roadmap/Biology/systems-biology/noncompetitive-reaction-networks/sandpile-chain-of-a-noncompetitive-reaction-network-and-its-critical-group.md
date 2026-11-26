# Sandpile Markov chain of a noncompetitive reaction network and its critical group

**Setting.** A chemical reaction network on $N$ species has reactions $\nu_r \to \nu'_r$ ($r = 1,\dots,d$) acting on states $c \in \mathbb{N}^N$. It is *active* at $c$ if $c \ge \nu_r$ for some $r$, and a state where no reaction can fire is *static*; $\operatorname{Stat}$ denotes the set of static states. The network is *noncompetitive* if every species whose count decreases in a reaction appears as a reactant in that reaction only, and *entirely execution bounded* if every execution from every state is finite (equivalently, the network has a linear potential function).

**Rate independence.** For a noncompetitive network, if $c$ reaches a static state $c'$ by an execution of length $\ell$, then no execution from $c$ is longer than $\ell$, every execution of length $\ell$ ends in $c'$, and every shorter one ends in a non-static state. Hence each static state $q$ and species $i$ determine a unique static state $R_i(q)$ reached from $q + e_i$.

**CRN sandpile Markov chain.** Let $\mu$ be a probability law on species. The chain on $\operatorname{Stat}$ moves by $q_{n+1} = R_{i_{n+1}}(q_n)$ with $i_1, i_2, \dots$ i.i.d. $\sim \mu$: add one molecule of a random species and let the network relax.

**Theorem.** Let the network be noncompetitive and entirely execution bounded, with finitely many static states reachable. Then
1. the network defines a finite irreducible Abelian network $\mathcal{N}$ (processors at the source complexes, a generalized toppling network on the graph of complexes) that halts on all inputs; its production matrix is $P_{ij} = \Gamma^p_{ij}/\Gamma^r_{jj}$ when $\Gamma^p_{ij} > 0$ and $0$ otherwise, independent of the recurrent state, where $\Gamma^r, \Gamma^p$ are the reactant and product stoichiometry matrices;
2. the recurrent states of the CRN sandpile chain are the recurrent states $\operatorname{Rec}\mathcal{N}$ of the Abelian network, and the critical group acts on them simply transitively, so

$$\#\operatorname{Rec}\mathcal{N} = \#\operatorname{Crit}\mathcal{N}, \qquad \operatorname{Crit}\mathcal{N} \cong \mathbb{Z}^{\mathcal{A}}/(I - P)K,$$

with $K$ the total kernel lattice of $\mathcal{N}$. In general only a fraction of the static states are recurrent.

## Depends on

## Expansion

Noncompetitiveness means firing one reaction never disables another, which is exactly the local abelian property of Abelian networks: the final static state does not depend on the order of firings. Each source complex becomes a processor that consumes its reactant species and emits product species; execution boundedness makes the network halt on all inputs. The Bond–Levine theory of Abelian networks then applies verbatim: the sandpile chain on a halting irreducible network has the critical group acting freely and transitively on recurrent states, generalizing the Dhar sandpile group of a graph, and its order is the determinant-type index of $(I-P)K$ in $\mathbb{Z}^{\mathcal{A}}$.

## Sources

- L. Faul, X. Richard, M. Betrisey and C. Mazza, "On the abelian structure of noncompetitive chemical reaction networks", arXiv:2512.17491 (2025), Definitions 2.5 and 4.3, Theorems 3.3, 3.4, Propositions 6.2, 6.3, 9.1 and Theorem 9.2, <https://doi.org/10.48550/arXiv.2512.17491>.
- B. Bond and L. Levine, "Abelian networks III: The critical group", Journal of Algebraic Combinatorics 43 (2016), Theorem 3.11, <https://doi.org/10.1007/s10801-015-0648-x>.
