# The second-price auction is the VCG mechanism with Clarke pivot payments

Let $I$ be a finite set of at least two agents, and let $w$ be a winner rule that picks a highest bid:
$t_j \le t_{w(t)}$ for every bid vector $t$ and every agent $j$. Use the agents as alternatives and the
alternative rule $f(v) = w\bigl((v_j(j))_{j \in I}\bigr)$. Then for every vector $t$ of nonnegative bids and
every agent $i$, the Groves payment with the Clarke pivot term at the single-item profile $v^t$ is the
second-price payment of agent $i$ at the bids $t$ (Nisan 2007, §9.3.5.1).

## Background

- [Clarke pivot term](clarke-pivot.md): with nonnegative bids, the others' best welfare without agent $i$ is the highest competing bid.

## Sources

- N. Nisan, "Introduction to mechanism design (for computer scientists)", Chapter 9 of N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, §9.3.5.1.
