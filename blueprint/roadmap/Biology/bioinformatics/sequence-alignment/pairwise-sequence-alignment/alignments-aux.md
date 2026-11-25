# Fuel-bounded enumeration of alignments

Define lists $L_n(x, y)$ of [alignments](alignment.md) by

- $L_0(x, y)$ is empty;
- $L_{n+1}(\text{empty}, \text{empty})$ contains only the empty alignment;
- $L_{n+1}(\text{empty}, b y)$ is $L_n(\text{empty}, y)$ with the column $(-, b)$ put in front of each alignment, and $L_{n+1}(a x, \text{empty})$ is $L_n(x, \text{empty})$ with $(a, -)$ in front;
- $L_{n+1}(a x, b y)$ is $L_n(x, y)$ with $(a, b)$ in front, followed by $L_n(x, b y)$ with $(a, -)$ in front, followed by $L_n(a x, y)$ with $(-, b)$ in front.
