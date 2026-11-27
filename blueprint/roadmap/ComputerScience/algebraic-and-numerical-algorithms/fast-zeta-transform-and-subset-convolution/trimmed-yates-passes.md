# Trimmed Yates passes

Process the coordinates of $[n]$ in a duplicate-free order $i_1, \dots, i_n$, so that stage $0$ is $t_0 = f$ and stage $j$ is $t_j(S) = t_{j-1}(S) + c\,[i_j \in S]\,t_{j-1}(S \setminus \{i_j\})$ for a fixed coefficient $c$. The value of stage $j$ at $S$ depends only on the values of stage $j - 1$ at $S$ and at $S \setminus \{i_j\}$. Consequently, for any family $\mathcal{F}$ of target sets, put $D_n = \mathcal{F}$ and $D_{j-1} = D_j \cup \{S \setminus \{i_j\} : S \in D_j\}$; computing each stage $j = 1, \dots, n$ forward only on $D_j$ (from $t_0 = f$ on $D_0$) yields $t_n$ on $\mathcal{F}$. Here $D_j$ consists of the sets obtained from members of $\mathcal{F}$ by deleting some of the *unprocessed* coordinates $i_{j+1}, \dots, i_n$, so every $D_j$ lies in the downward closure of $\mathcal{F}$, and if $\mathcal{F}$ is downward closed then $D_j = \mathcal{F}$ for every $j$. (Closure in the processed coordinates is not enough: with order $(1, 2)$ and $\mathcal{F} = \{\{2\}\}$, stage $2$ at $\{2\}$ needs stage $1$ at $\varnothing$.) This is distinct from trimming upward from the support of the input.

## Depends on

- [Yates's algorithm computes zeta and Möbius transforms in n 2^n operations](yates-algorithm.md)

## Sources

- A. Björklund, T. Husfeldt, P. Kaski and M. Koivisto, "Trimmed Moebius Inversion and Graphs of Bounded Degree", Theory of Computing Systems 47(3), 2010.
