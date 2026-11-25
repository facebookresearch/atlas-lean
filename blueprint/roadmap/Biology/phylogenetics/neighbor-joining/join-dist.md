# Cluster dissimilarity after a neighbor-joining step

For a cluster dissimilarity $D$ and clusters $a, b$, the dissimilarity after joining $a$ and $b$ is

$$D'(u, v) = \begin{cases} 0 & u = v = a \cup b,\\ \frac12\bigl(D(a, v) + D(b, v) - D(a, b)\bigr) & u = a \cup b \ne v,\\ \frac12\bigl(D(a, u) + D(b, u) - D(a, b)\bigr) & v = a \cup b \ne u,\\ D(u, v) & \text{otherwise.}\end{cases}$$
