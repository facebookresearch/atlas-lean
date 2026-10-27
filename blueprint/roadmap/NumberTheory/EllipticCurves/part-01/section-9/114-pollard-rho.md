---
article_id: af_fce332e24b9453e14e1380d9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: pollardRho_dlog_extraction
---

# Algorithm 9.5 (Pollard-$\rho$)

Given $\alpha$, $N=|\alpha|$, $\beta \in \langle\alpha\rangle$, compute
 $\log_{\alpha} \beta$ as follows: 1. Compute $\delta_{i}=c_{i} \alpha+d_{i}
 \beta$ for $r \approx 20$ randomly chosen pairs $c_{i}, d_{i} \in
 \mathbb{Z}/N\mathbb{Z}$. 2. Compute $\gamma_{0}=a_{0} \alpha+b_{0} \beta$
 for randomly chosen $a_{0}, b_{0} \in \mathbb{Z}/N\mathbb{Z}$. 3. Compute
 $(a_{j}, b_{j}, \gamma_{j})=f(a_{j-1}, b_{j-1}, \gamma_{j-1})$ for
 $j=1,2,3,\ldots$, until $\gamma_{k}=\gamma_{j}$ with $k>j$. 4. The collision
 $\gamma_{k}=\gamma_{j}$ implies $a_{j} \alpha+b_{j} \beta=a_{k} \alpha+b_{k}
 \beta$. Provided that $b_{k}-b_{j}$ is invertible in
 $\mathbb{Z}/N\mathbb{Z}$, we return $\log_{\alpha}
 \beta=\frac{a_{j}-a_{k}}{b_{k}-b_{j}} \in \mathbb{Z}/N\mathbb{Z}$; otherwise
 start over at step 1.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.783 Elliptic Curves (Spring 2021), Section 9.8](../../../../../sources/v1/EllipticCurves.md)
