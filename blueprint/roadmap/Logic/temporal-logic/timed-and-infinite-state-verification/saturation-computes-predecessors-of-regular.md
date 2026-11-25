# Saturation computes predecessors of regular sets of pushdown configurations

A pushdown system $\mathcal{P} = (P, \Gamma, \Delta)$ has finite sets $P$ of control locations and $\Gamma$ of stack symbols and a finite set $\Delta$
of rules $\langle p, \gamma \rangle \hookrightarrow \langle p', w \rangle$ with $p, p' \in P$, $\gamma \in \Gamma$ and $w \in \Gamma^*$. Configurations are pairs $\langle p, w \rangle$ with
$w \in \Gamma^*$, and such a rule gives the step $\langle p, \gamma w' \rangle \Rightarrow \langle p', w w' \rangle$ for every $w' \in \Gamma^*$. A *$\mathcal{P}$-automaton* is a finite
automaton $\mathcal{A} = (Q, \Gamma, \to_0, P, F)$ over the alphabet $\Gamma$ whose set of initial states is $P \subseteq Q$; it accepts $\langle p, w \rangle$ if
$p \xrightarrow{w} q$ for some $q \in F$. For a set $C$ of configurations, $\mathrm{pre}^*(C)$ is the set of configurations from which some
configuration of $C$ is reachable in zero or more steps.

Assume that $\mathcal{A}$ has no transition into an initial state. Apply the saturation rule

> if $\langle p, \gamma \rangle \hookrightarrow \langle p', w \rangle \in \Delta$ and $p' \xrightarrow{w} q$ in the current automaton, add the transition $(p, \gamma, q)$

until no transition can be added. Then:

- the procedure terminates, since it adds no states and only finitely many transitions exist;
- the resulting automaton $\mathcal{A}_{\mathrm{pre}^*}$ accepts exactly $\mathrm{pre}^*(L(\mathcal{A}))$;
- if every rule has $|w| \le 2$, $\mathcal{A}_{\mathrm{pre}^*}$ can be computed in time $O(|Q|^2 |\Delta|)$ and space $O(|Q|\,|\Delta| + |\to_0|)$. Every pushdown
  system can be brought into this form by splitting rules through fresh control locations, and the same bound then holds for
  general systems after the auxiliary transitions are removed.

## Sources

- S. Schwoon, *Model-checking pushdown systems*, PhD thesis, Technische Universität München, 2002, <http://www.lsv.fr/Publis/PAPERS/PDF/schwoon-phd02.pdf>: Theorem 3.1 (normal form), Definition 3.2 ($\mathcal{P}$-automata), Section 3.1.1 (saturation rule and the no-transition-into-initial-states assumption), Lemmas 3.1–3.2, Theorem 3.2 and Theorem 3.4 with the following remark on general systems.
- A. Bouajjani, J. Esparza and O. Maler, "Reachability analysis of pushdown automata: application to model-checking", *CONCUR 1997*, LNCS 1243, Springer, 1997: the original saturation procedure and its correctness proof.
