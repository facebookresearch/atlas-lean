# Whether a one-counter VASS language is boundedly ambiguous is undecidable

For a one-dimensional vector addition system with states that reads letters and accepts by control state, it is undecidable whether its language is recognized by some unambiguous, $k$-ambiguous, boundedly ambiguous or deterministic VASS, and more generally whether it belongs to any class that lies between the regular languages and the boundedly ambiguous VASS languages.

**Setting (Czerwiński and Orlikowski).** A $d$-dimensional *vector addition system with states* ($d$-VASS) $V = (\Sigma, Q, \delta, I, F)$ is a finite automaton over the alphabet $\Sigma$, without $\varepsilon$-transitions, with $d$ counters over $\mathbb N$; each transition $(s, a, \vec v, s') \in \delta \subseteq Q \times \Sigma \times \mathbb Z^d \times Q$ reads the letter $a$ and adds $\vec v$ to the counters, and is enabled only if no counter becomes negative. Configurations are pairs $s(\vec u) \in Q \times \mathbb N^d$; $I$ is a finite set of initial configurations and $F$ a finite set of final configurations, and a run is accepting if it starts in $I$ and ends in a configuration covering one of $F$. The language $L(V)$ is the set of words read by accepting runs. The VASS *accepts by states* when acceptance depends only on the final control state. $V$ is *$k$-ambiguous* if every word of $L(V)$ has at most $k$ accepting runs, *unambiguous* if it is $1$-ambiguous, and *boundedly ambiguous* if it is $k$-ambiguous for some $k$; a language is a $k$-ambiguous (boundedly ambiguous) VASS language if some such VASS, of any dimension, recognizes it.

**Theorem (Czerwiński and Orlikowski).** Let $\mathcal C$ be any class of languages that contains all regular languages and is contained in the class of boundedly ambiguous VASS languages. Then it is undecidable whether the language of a given $1$-VASS accepting by states belongs to $\mathcal C$. In particular it is undecidable whether such a language is recognized by some unambiguous VASS, by some $k$-ambiguous VASS for a given $k$, by some boundedly ambiguous VASS, by some deterministic VASS, or by some $k$-ambiguous $1$-VASS for a given $k$.

The theorem also yields the known undecidability of regularity and of determinizability for $1$-VASS. In contrast, the same paper shows that regularity is decidable for boundedly ambiguous VASS.

## Depends on

- [Decidability by multi-stack machines](../../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Finiteness of reachability sets of lossy counter machines is Σ⁰₁-complete](../../../../distributed-execution-models/parameterized-and-infinite-state-verification/lossy-counter-machines/finiteness-for-lossy-counter-machines-sigma01-complete.md)

## Expansion

The reduction is from the problem whether a lossy counter machine started in a given state with all counters zero has a finite reachability set, which is undecidable by Mayr's theorem in the form strengthened to the zero initial configuration by Almagor and Yeshurun; a complete expansion needs that zero-start version. The machine is first modified so that its runs can end by moving all counter values into the first counter and then decrementing it, and $L_{M}$ is the language encoding its correct runs in reverse order. The complement of $L_M$ is recognized by an effectively constructed $1$-VASS accepting by states. If the reachability set is finite, $L_M$ and its complement are regular; if it is infinite, a pumping lemma for $k$-ambiguous VASS languages (the paper's first main lemma) shows that the complement is not a boundedly ambiguous VASS language. So membership of the constructed language in $\mathcal C$ decides finiteness.

## Sources

- Wojciech Czerwiński and Łukasz Orlikowski, "Languages of Boundedly-Ambiguous Vector Addition Systems with States", in *36th International Conference on Concurrency Theory (CONCUR 2025)*, Leibniz International Proceedings in Informatics 348, Schloss Dagstuhl, 2025, pp. 13:1–13:23, doi:[10.4230/LIPIcs.CONCUR.2025.13](https://doi.org/10.4230/LIPIcs.CONCUR.2025.13); read in arXiv:2504.07669v2 ([arXiv](https://arxiv.org/abs/2504.07669v2)), whose numbering is used: Theorem 1 and Corollary 2 (introduction), the definitions of VASS, their languages and $k$-ambiguity in the preliminaries, the proof of Theorem 1 in the section devoted to it, and the regularity theorem for boundedly ambiguous VASS.
