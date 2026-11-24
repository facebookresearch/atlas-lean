# Kinship coefficient by Malécot's recursion

In a [pedigree](pedigree.md) with parents $(f(i), m(i))$, the tabular kinship $\varphi_{ij}$ is defined by recursion on $i + j$:

- if $j < i$: $\varphi_{ij} = 0$ when $i$ is a founder, and $\varphi_{ij} = \frac12(\varphi_{f(i) j} + \varphi_{m(i) j})$ otherwise;
- if $i < j$: $\varphi_{ij} = 0$ when $j$ is a founder, and $\varphi_{ij} = \frac12(\varphi_{i f(j)} + \varphi_{i m(j)})$ otherwise;
- if $i = j$: $\varphi_{ii} = \frac12$ when $i$ is a founder, and $\varphi_{ii} = \frac12(1 + \varphi_{f(i) m(i)})$ otherwise.
