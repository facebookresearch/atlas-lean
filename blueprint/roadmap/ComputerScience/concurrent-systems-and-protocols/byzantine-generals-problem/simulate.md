# Three generals simulating a protocol

Let $P$ be an oral-message protocol for the
generals $G$ with orders in $V$, states $\sigma$ and messages $M$, let $c \in G$, let
$\mathrm{grp} : G \to \{0, 1, 2\}$ split the generals into three groups and let
$\mathrm{rep} : \{0, 1, 2\} \to G$. The simulation of $P$ with $c$, $\mathrm{grp}$ and
$\mathrm{rep}$ is the oral-message protocol for the generals $\{0, 1, 2\}$ with orders in $V$,
whose states are families $(s(i))_{i \in G}$ of states of $\sigma$ and whose messages are
families $(\mu(j, i))_{j, i \in G}$ of messages of $M$, defined as follows. A general other
than the commander starts from the family of the initial states that $P$ gives each general of
$G$ as a non-commander; the commander, with order $v$, starts from the family of the initial
states of the generals of $G$ in $P$ when $c$ is the commander with order $v$. In round $r$, a
general in state $s$ sends every general the family whose entry $(j, i)$ is the message that
general $j$ of $P$, in state $s(j)$, sends to general $i$ in round $r$. In round $r$, general
$g$ in state $s$, having received $\mu_h$ from each general $h$, moves to the family that keeps
$s(i)$ for each $i$ with $\mathrm{grp}(i) \ne g$ and, for each $i$ with $\mathrm{grp}(i) = g$,
holds the state to which general $i$ of $P$ moves in round $r$ from $s(i)$ on receiving
$\mu_{\mathrm{grp}(j)}(j, i)$ from each $j \in G$. General $g$ in final state $s$ decides
what general $\mathrm{rep}(g)$ of $P$ decides in state $s(\mathrm{rep}(g))$.
