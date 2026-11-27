# Qualitative Büchi and Streett objectives for probabilistic lossy channel systems are undecidable

In lossy channel systems where a scheduler resolves nondeterminism and each stored message is lost with a fixed probability at every step, it is undecidable whether some scheduler visits a set of locations infinitely often with positive probability, and whether some scheduler satisfies a Streett condition almost surely, with positive probability, with probability less than one, or with probability zero.

**Setting (Baier, Bertrand and Schnoebelen).** A [lossy channel system](lossy-channel-systems.md) $\mathcal{L} = (Q, C, M, \Delta)$ has finitely many control locations $Q$, channels $C$, messages $M$ and rules $q \xrightarrow{op} p$ with $op$ a send $c!m$, a receive $c?m$ or an internal action; every location has a rule that is not a receive. An *NPLCS* $\mathcal{N} = (\mathcal{L}, \tau)$ adds a *fault rate* $\tau \in (0, 1)$ and is a Markov decision process: a *scheduler* $\mathcal{U}$ chooses, from the history, an enabled rule, which is fired perfectly, and then each message in the channels is lost independently with probability $\tau$. For an LTL property $\varphi$ over locations, $\Pr_{\mathcal{U}}((q, \varepsilon) \models \varphi)$ is the probability that a run from location $q$ with empty channels satisfies $\varphi$; $\Box \Diamond A$ means that a location in $A$ is visited infinitely often.

**Theorem (Baier, Bertrand and Schnoebelen).**

1. It is undecidable, given an NPLCS $\mathcal{N}$, a location $q$ and a set $A$ of locations, whether some scheduler $\mathcal{U}$ has $\Pr_{\mathcal{U}}((q, \varepsilon) \models \Box \Diamond A) > 0$.
2. For each of the conditions $> 0$, $< 1$, $= 1$ and $= 0$, it is undecidable, given $\mathcal{N}$, $q$ and sets $A_1, B_1, \dots, A_n, B_n$ of locations, whether some scheduler $\mathcal{U}$ satisfies the condition for $\Pr_{\mathcal{U}}\bigl((q, \varepsilon) \models \bigwedge_{i=1}^n (\Box \Diamond A_i \to \Box \Diamond B_i)\bigr)$.

In particular, qualitative LTL model checking over all schedulers is undecidable. The same paper proves these problems decidable when schedulers are restricted to finite memory, and proves qualitative reachability and almost-sure repeated reachability decidable over all schedulers.

## Depends on

- [Lossy channel systems](lossy-channel-systems.md)
- [Formulas of linear temporal logic](../../../../Logic/temporal-logic/linear-temporal-logic/formula.md)
- [Markov decision processes and adversaries](../../../../Logic/temporal-logic/probabilistic-model-checking/markov-decision-processes-and-adversaries.md)
- [Markov decision process](../../../heuristic-search-and-planning/value-iteration/mdp.md)

## Proof depends on

None.

## Expansion

Both clauses reduce from the boundedness problem for lossy channel systems, which Mayr proved undecidable. The system $\mathcal{L}$ is extended with a cleaning gadget that empties the channels and returns to the initial configuration, a success location and a sink. If $\mathcal{L}$ is bounded from its initial configuration, every scheduler that visits the success location infinitely often ends in the sink almost surely; if it is unbounded, an infinite-memory scheduler that runs $\mathcal{L}$ to ever larger configurations before each visit to the success location avoids the sink with positive probability, because the probability of losing all messages of a large configuration tends to zero. Clause 2 combines a variant of this construction with Boolean identities among Streett conditions. A good expansion adds and links a page for the undecidability of boundedness of lossy channel systems.

## Sources

- Christel Baier, Nathalie Bertrand and Philippe Schnoebelen, *Verifying nondeterministic probabilistic channel systems against ω-regular linear-time properties*, ACM Transactions on Computational Logic 9 (2007), no. 1, article 5, https://doi.org/10.1145/1297658.1297663; Section 2 (NPLCS and schedulers), the single Büchi undecidability theorem and the Streett undecidability theorem in the section on hardness and undecidability, read in arXiv:cs/0511023v3. Locators in arXiv:cs/0511023v3: Theorem 5.7, Lemma 5.12 and Theorem 5.13.
