# Exponential mechanism

For real parameters $\varepsilon$ and $\Delta$, a utility score $u$ and a finite nonempty range $R$,
the exponential mechanism on database $x$ is the probability measure on $R$ that gives each output $r$
the [probability](exp-mech-prob.md) $p_x(r)$, proportional to $\exp(\varepsilon u(x, r) / (2\Delta))$.
For privacy, $\Delta$ should bound the sensitivity $\max_r \max_{x \sim y} |u(x, r) - u(y, r)|$ of the
score in its database argument; the score may be arbitrarily sensitive in $r$. The range must not depend on the database. It is the natural mechanism
for selecting a best non-numeric answer, such as a price in an auction, where adding noise to the
answer itself would destroy its value.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/privacybook.html>, Definition 3.4 and the discussion before it (Example 3.5).
- F. McSherry and K. Talwar, *Mechanism design via differential privacy*, FOCS 2007 (the exponential mechanism, cited in Dwork and Roth 2014, Section 3.7).
