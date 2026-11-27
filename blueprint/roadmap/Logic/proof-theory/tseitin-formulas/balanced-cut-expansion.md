# Ben-Sasson–Wigderson expansion of a multigraph

For a finite multigraph $G = (V,E)$ and $U \subseteq V$, let $E(U, V \setminus U)$ be the set of edges with exactly one endpoint in $U$. The *expansion* (minimum balanced cut) of $G$ is

$$e(G) = \min\{\, |E(U, V\setminus U)| : |V|/3 \le |U| \le 2|V|/3 \,\}.$$

The *edge expansion* $h(G)$ is the minimum of $|E(U, V\setminus U)|/|U|$ over nonempty $U$ with $|U| \le |V|/2$. One has $e(G) \ge h(G)|V|/3$; in particular $h(G) > 0$ implies that $G$ is connected and $e(G)$ is linear in $|V|$.

## Sources

- E. Ben-Sasson and A. Wigderson, "Short Proofs Are Narrow — Resolution Made Simple", Journal of the ACM 48(2), 149–169, 2001: Definition 4.3.
