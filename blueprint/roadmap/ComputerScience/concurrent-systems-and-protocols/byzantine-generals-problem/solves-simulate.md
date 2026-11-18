# Simulation reduces many generals to three

Let $P$ be an oral-message protocol for a
finite set $G$ of generals, let $c \in G$ and $m, T \in \mathbb{N}$, and suppose that $P$ solves
the Byzantine generals problem with commander $c$ and at most $m$ traitors in $T$ rounds. Let
$\mathrm{grp} : G \to \{0, 1, 2\}$ and $\mathrm{rep} : \{0, 1, 2\} \to G$ satisfy
$\mathrm{grp}(c) = 0$, $\mathrm{grp}(\mathrm{rep}(g)) = g$ for every $g \ne 0$, and
$|\{i \in G : \mathrm{grp}(i) = g\}| \le m$ for every $g$. Then the simulation of $P$ with $c$,
$\mathrm{grp}$ and $\mathrm{rep}$ solves the Byzantine generals problem for the generals
$\{0, 1, 2\}$ with commander $0$ and at most one traitor in $T$ rounds.
