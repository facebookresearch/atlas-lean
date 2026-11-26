# Transient-to-transient entry of a time-ordered Nelson–Aalen product for competing risks

Let $k$ and $r$ be natural numbers. Grouped competing-risks data consist of strictly increasing observation times $t_0 < \dots < t_{k-1}$, the number $d_{j,c}$ of failures from cause $c \in \{0, \dots, r-1\}$ at $t_j$, and the number $w_j$ of subjects censored at $t_j$. Write $d_j = \sum_{c} d_{j,c}$ and $Y_j = \sum_{l \ge j} (d_l + w_l)$ for the number at risk at $t_j$.

As multi-state data on the states $\{\star\} \sqcup \{0, \dots, r-1\}$ ($\star$ the transient state, a cause $c$ the absorbing state "failed from cause $c$"), the only transitions at $t_j$ are $\star \to c$, numbering $d_{j,c}$; the number at risk in $\star$ at $t_j$ is $Y_j$, and the number at risk in every absorbing state is $0$. The Nelson–Aalen jump at $t_j$ is the matrix $\Delta_j$ with

$$\Delta_j(h, l) = \frac{N_{hl}(t_j)}{Y_h(t_j)} \ (h \ne l), \qquad \Delta_j(h, h) = -\frac{\sum_{l' \ne h} N_{hl'}(t_j)}{Y_h(t_j)},$$

where $N_{hl}(t_j)$ and $Y_h(t_j)$ are these transition and at-risk numbers, with real division, $x/0 = 0$.

For a set of active indices given by a predicate on $\{0, \dots, k-1\}$, the time-ordered product of the Nelson–Aalen jumps is $O(\Delta) = M_0 M_1 \cdots M_{k-1}$, with $I$ the identity matrix, $M_j = I + \Delta_j$ if $j$ is active and $M_j = I$ otherwise (the identity when $k = 0$).

For every set of active indices,

$$O(\Delta)(\star, \star) = \prod_{j=0}^{k-1} \begin{cases} 1 - d_j / Y_j & \text{if } j \text{ is active}, \\ 1 & \text{otherwise,} \end{cases}$$

with $d_j / Y_j = 0$ when $Y_j = 0$; the factors $1 - d_j / Y_j$ are the Kaplan–Meier factors of the cause-blind data.
