# Output probabilities of the exponential mechanism

On a finite nonempty range $R$, the exponential mechanism outputs $r$ on database $x$ with probability

$$
p_x(r) = \frac{\exp(\varepsilon u(x, r) / (2\Delta))}{\sum_{r' \in R} \exp(\varepsilon u(x, r') / (2\Delta))}.
$$

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/privacybook.html>, Definition 3.4.
- F. McSherry and K. Talwar, *Mechanism design via differential privacy*, FOCS 2007 (the exponential mechanism, cited in Dwork and Roth 2014, Section 3.7).
