# Combinatorial agency and the price of unaccountability

In *combinatorial agency*, $n$ agents each choose to exert effort (cost $c_i > 0$) or not; a technology maps the effort profile $a$ to a success probability $t(a)$, strictly increasing in each agent's effort, with $t(a) > 0$ for every $a$. A principal valuing success at $v > 0$ offers contracts paying agent $i$ an amount $p_i \ge 0$ upon success and nothing upon failure (limited liability), so agent $i$'s utility is $p_i t(a) - c_i a_i$ and the principal's is $t(a)(v - \sum_i p_i)$. The contract inducing a target set of exerting agents as a Nash equilibrium with minimal expected payment pays each exerting agent $c_i / \Delta_i(a_{-i})$, where $\Delta_i(a_{-i}) = t(1, a_{-i}) - t(0, a_{-i})$ is $i$'s marginal contribution to the success probability, and pays $0$ to every other agent. Write $t(S)$ for the success probability when exactly the agents in $S$ exert effort, $S^*(v)$ for a set maximizing the principal's hidden-action utility $t(S)\bigl(v - \sum_{i \in S} c_i / (t(S) - t(S \setminus \{i\}))\bigr)$, and $S^*_{oa}(v)$ for a set maximizing the first-best welfare $t(S)\,v - \sum_{i \in S} c_i$ (effort observable, each exerting agent paid its cost). The *price of unaccountability* of $t$ is

$$
\mathrm{POU}(t) = \sup_{v > 0} \frac{t(S^*_{oa}(v))\,v - \sum_{i \in S^*_{oa}(v)} c_i}{t(S^*(v))\Bigl(v - \sum_{i \in S^*(v)} \frac{c_i}{t(S^*(v)) - t(S^*(v) \setminus \{i\})}\Bigr)},
$$

the worst-case ratio of the first-best welfare to the principal's expected utility under the optimal hidden-action contract.

## Depends on

- [Strategic Game](../../not-yet-classified/part-02/strategic-game/strategic-game.md)
- [Pure Nash equilibrium of a finite game](../../noncooperative-games/potential-games/is-pure-nash-2.md)

## Sources

- Moshe Babaioff, John Chuang and Michal Feldman, "Incentives in Peer-to-Peer Systems", Algorithmic Game Theory, Cambridge University Press, 2007.
