# Model checking iterated public announcements over regular Kripke structures is undecidable

Parameterized public announcement logic reasons about the knowledge of arbitrarily many agents in a regular Kripke structure, where states are words with one letter per agent. Its model checking is decidable, but adding an operator that iterates an announcement arbitrarily often makes model checking undecidable for some fixed structure.

**Setting (Stan and Lin).** A *parameterized Kripke structure* $\mathcal{M} = (S, AP, \to, L, |\cdot|)$ has a set $S$ of states, each with a size $|s| \in \mathbb{N}$ (the number of agents), a finite set $AP$ of atomic propositions with labelings $L_i(s) \subseteq AP$ for $0 \le i < |s|$, and reflexive indistinguishability relations $s \to_i s'$ between states of equal size, meaning that in $s$ agent $i$ considers $s'$ possible. It is *regular* if $S \subseteq \Sigma^*$ for an alphabet $\Sigma$, $|s|$ is the length of $s$, $L_i(s)$ depends only on the letter $s[i]$, and the language of convolutions of $s$, a one-hot encoding of $i$, and $t$ over all $s \to_i t$ is regular. Formulas of *parameterized public announcement logic* (PPAL) are built from $\top$, $\neg$, $\wedge$, index quantifiers $\exists i$, index constraints $i = 0$, $i \bmod k = 0$, $i = j + k$, indexed atoms $p_i$, the possibility operator $\langle i \rangle \varphi$ (some state that agent $i$ considers possible satisfies $\varphi$), and public announcements $[\varphi]\psi$, which hold if $\psi$ holds in the structure restricted to the states satisfying $\varphi$ whenever $\varphi$ holds. PPAL$^*$ adds iterated announcements $[\varphi]^* \psi$, satisfied where $[\varphi][\varphi] \cdots [\varphi]\psi$ with $k$ announcements holds for some $k \ge 0$.

**Theorem (Stan and Lin).** There is a regular Kripke structure $\mathcal{M}$ such that no algorithm decides, given a closed PPAL$^*$ formula $\varphi$, whether some state of $\mathcal{M}$ satisfies $\varphi$ (Theorem 4.5(2)). The source's regular model-checking problem asks exactly this: whether the satisfaction set of $\varphi$ in $\mathcal{M}$ is empty.

The source also shows that for some regular structure, model checking against PPAL formulas is non-elementary (Theorem 4.5(1)), using an automatic structure of To whose modal theory is non-elementary.

For every regular Kripke structure and closed PPAL formula, the set of states satisfying the formula is regular and computable, so PPAL model checking is decidable; the iterated announcement operator is what breaks decidability.

## Depends on

- [Epistemic models](../../../Logic/modal-logic/epistemic-logic/model.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Proof sketch

The structure $\mathcal{M}$ has propositions $p, c^{(0)}, c^{(1)}$, and its indistinguishability transducer relates all states of equal length for every agent; the formula uses only agent $0$. A first announcement keeps only words in which each proposition holds at exactly one position, so that a word encodes a configuration $(q, x_0, x_1)$ of a deterministic two-counter machine by the positions of $p$, $c^{(0)}$ and $c^{(1)}$. The formula is $p_{q_0} \wedge c^{(0)}_0 \wedge c^{(1)}_0 \wedge [\varphi_m][\varphi_t]^* \bot$, where $\varphi_m$ is that first announcement and $\varphi_t$ states, using the possibility operator of agent $0$ and index arithmetic for increments, decrements and zero tests, that the current configuration is not final and has a successor. Each announcement of $\varphi_t$ removes the encodings with no remaining successor, starting from the final configuration, and with vacuous truth $[\varphi_t]^* \bot$ holds at a state exactly when it is removed after finitely many announcements. So the formula is satisfied in some state exactly when the deterministic machine reaches its final state from $(q_0, 0, 0)$. The halting problem for two-counter machines started with both counters at $0$ is stated on the linked universality page.

## Sources

- Daniel Stan and Anthony W. Lin, *Regular Model Checking Approach to Knowledge Reasoning over Parameterized Systems*, Proceedings of the 20th International Conference on Autonomous Agents and Multiagent Systems (AAMAS 2021), IFAAMAS, 2021, pp. 1254–1262; Definitions of parameterized and regular Kripke structures, PPAL and PPAL$^*$, Theorem 4.1 and Theorem 4.5, read in the open-access copy at https://www.ifaamas.org/Proceedings/aamas2021/pdfs/p1254.pdf and in arXiv:2102.04361v3.
