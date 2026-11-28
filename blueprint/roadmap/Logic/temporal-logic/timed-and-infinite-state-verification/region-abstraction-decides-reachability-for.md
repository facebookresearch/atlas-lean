# Region abstraction decides reachability for timed automata

Let $\mathcal{A}$ be a timed automaton with locations $S$, initial locations $S_0$, clocks $C$ and edges $(s, s', a, \lambda, \delta)$ carrying
a clock constraint $\delta$ and a set $\lambda \subseteq C$ of clocks to reset, and use the
[clock regions](clock-regions-of-timed-automata.md) of $\mathcal{A}$. A region $\alpha'$ is a *time-successor* of a region $\alpha$ if for each
$\nu \in \alpha$ there is a positive $t \in \mathbb{R}$ with $\nu + t \in \alpha'$, matching the strictly increasing time
sequences of timed runs. The *region automaton* $R(\mathcal{A})$ has states $(s, \alpha)$, initial states $(s_0, [\mathbf{0}])$
for $s_0 \in S_0$, and an $a$-labelled edge from $(s, \alpha)$ to $(s', \alpha')$ whenever $\mathcal{A}$ has an edge $(s, s', a, \lambda, \delta)$ and a
time-successor $\alpha''$ of $\alpha$ satisfies $\delta$ and $\alpha' = [\lambda \mapsto 0]\alpha''$.

- $R(\mathcal{A})$ is finite: it has at most $|S|$ times the number of clock regions states.
- The projection $(s_i, [\nu_i])_i$ of every run $(s_i, \nu_i)_i$ of $\mathcal{A}$ is a run of $R(\mathcal{A})$ over the same letters.
- Conversely, every progressive run of $R(\mathcal{A})$, one in which every clock $x$ infinitely often lies in a region satisfying
  $x = 0 \vee x > c_x$, is the projection of a run of $\mathcal{A}$ over some time sequence.
- Emptiness of the language of a timed Büchi automaton is decidable by searching $R(\mathcal{A})$ for a progressive accepting
  run, and it is PSPACE-complete.

Location reachability reduces to emptiness: make the target location the only accepting one and give it a self-loop
with no constraint and no reset. A finite run reaching it then extends to a time-divergent accepting run, so location
reachability is decidable in polynomial space.

## Depends on

- [Clock regions of timed automata](clock-regions-of-timed-automata.md)

## Proof depends on

- [Clock regions of timed automata](clock-regions-of-timed-automata.md)

## Sources

- R. Alur and D. L. Dill, "A theory of timed automata", *Theoretical Computer Science* 126(2):183–235, 1994: Definitions 4.6, 4.8, 4.10 and 4.11, the size bound on $R(\mathcal{A})$ after Example 4.9, Lemma 4.13 and Theorems 4.14, 4.16 and 4.17.
