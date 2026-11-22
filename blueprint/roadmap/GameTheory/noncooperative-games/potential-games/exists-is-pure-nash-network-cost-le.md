# Price of stability of fair cost sharing is at most H(k)

In the fair cost-sharing game with $k$ players and finitely many strategies, nonempty for every
player, there is a pure Nash equilibrium $s$ whose network costs at most $H(k)$ times the network
of every profile $t$:

$$\sum_{e : n_e(s) > 0} c_e \le H(k) \sum_{e : n_e(t) > 0} c_e .$$

Taking $t$ optimal, the price of stability is at most $H(k) = O(\log k)$; the bound is tight.

The equilibrium is a minimiser of Rosenthal's potential, and the proof chains
$\text{cost}(s) \le \Phi(s) \le \Phi(t) \le H(k)\, \text{cost}(t)$.

## Informally uses

- [Network cost is at most the potential](network-cost-le-potential.md),
  [Potential is at most H(k) times the network cost](potential-le-harmonic-mul-network-cost.md) and
  [Potential minimisers are Nash equilibria](is-pure-nash-of-forall-le.md).

## Sources

- E. Anshelevich, A. Dasgupta, J. Kleinberg, É. Tardos, T. Wexler and T. Roughgarden, "The price of stability for network design with fair cost allocation", SIAM J. Comput. 38(4) (2008), 1602–1623, Theorem 2.1.
- J. Kleinberg and É. Tardos, *Algorithm Design*, Addison-Wesley, 2005, §12.7.
