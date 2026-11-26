# Honest observations of a polynomial commitment

Fix the public key $k$, with field $\mathbb F_p$ and bound $t$, and a batch $Q$ of distinct field points chosen before commitment, with $|Q|<p$. The following joint distribution keeps the sampled polynomial for the mathematical experiment; only the view is sent to the observer.

1. Draw $t+1$ uniform coefficients. The coefficient map is a bijection from formal polynomials of degree at most $t$ to $\mathbb F_p^{t+1}$, so every bounded polynomial $f$ has mass $p^{-(t+1)}$, including zero.
2. Commit honestly to $f$, obtaining $(c,d)$. Take the first $\min(|Q|,\operatorname{natDegree}(f))$ entries of $Q$. Constants and zero have natural degree zero.
3. At each of these points $i$, independently sample an honest witness using the **same** $k,f,d$. Return the pair consisting of $f$ and the view $(c,[(i,f(i),w_i)])$. Every triple verifies against $c$ by honest correctness.

The order, values, witnesses and number of answers are visible. The decommitment information is not an input to the observer. In particular, the bound $t$ does not entitle it to $t$ answers when the sampled polynomial has smaller degree. This is an ordered, nonadaptive disclosure model for the collection in Definition 3.1; prediction happens **after** the view is observed.

## Source

A. Kate, G. M. Zaverucha and I. Goldberg, [*Polynomial Commitments*](https://cacr.uwaterloo.ca/techreports/2010/cacr2010-10.pdf), CACR 2010-10, §3.1, Definition 3.1, pp. 5–6.
