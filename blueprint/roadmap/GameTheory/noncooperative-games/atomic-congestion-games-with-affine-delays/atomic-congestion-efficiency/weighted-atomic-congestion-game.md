# Weighted atomic congestion game

A *weighted atomic congestion game* has players $i$ with weights $w_i \ge 0$ and finite strategy sets, each strategy $a$ selecting a finite set of resources $R_i(a)$. The load of resource $e$ under profile $s$ is $L_e(s) = \sum_{i : e \in R_i(s_i)} w_i$, player $i$ pays $w_i \sum_{e \in R_i(s_i)} \ell_e(L_e(s))$, and the social cost is $\sum_e L_e(s)\, \ell_e(L_e(s))$. Unit weights recover ordinary congestion games.

## Depends on

- [Congestion game](../../potential-games/congestion-game.md)

## Sources

- Noam Nisan, Tim Roughgarden, Eva Tardos and Vijay V. Vazirani, "Algorithmic Game Theory", Cambridge University Press, 2007.
- Baruch Awerbuch, Yossi Azar and Amir Epstein, "The Price of Routing Unsplittable Flow", Proceedings of the 37th Annual ACM Symposium on Theory of Computing, 2005.
