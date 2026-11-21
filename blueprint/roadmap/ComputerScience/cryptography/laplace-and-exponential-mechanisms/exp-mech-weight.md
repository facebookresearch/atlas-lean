# Weights of the exponential mechanism

For a utility score $u : X \times R \to \mathbb{R}$ and real numbers $\varepsilon$ and $\Delta$ (a
bound on the sensitivity of $u$), the exponential mechanism gives output $r$ on database $x$ the
un-normalised weight $\exp(\varepsilon u(x, r) / (2\Delta))$, where the exponent is read as $0$ when
$\Delta = 0$. Half of the privacy budget pays for the change of the
normalising constant between neighbours.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/privacybook.html>, Definition 3.4.
- F. McSherry and K. Talwar, *Mechanism design via differential privacy*, FOCS 2007 (the exponential mechanism, cited in Dwork and Roth 2014, Section 3.7).
