# Fuel-bounded enumeration of two-alphabet alignments

For sequences $x$ over an alphabet $A$ and $y$ over an alphabet $B$, define lists $L_n(x, y)$ of column lists (columns $(u, v)$ with $u \in A \cup \{-\}$, $v \in B \cup \{-\}$) by

- $L_0(x, y)$ is empty and $L_{n+1}(\text{empty}, \text{empty})$ contains only the empty list;
- $L_{n+1}(\text{empty}, b y)$ is $L_n(\text{empty}, y)$ with $(-, b)$ put in front of each entry, and $L_{n+1}(a x, \text{empty})$ is $L_n(x, \text{empty})$ with $(a, -)$ in front;
- $L_{n+1}(a x, b y)$ is $L_n(x, y)$ with $(a, b)$ in front, followed by $L_n(x, b y)$ with $(a, -)$ in front, followed by $L_n(a x, y)$ with $(-, b)$ in front.
