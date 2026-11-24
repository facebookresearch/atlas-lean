# Laplace mechanism

For a real-valued query $f : X \to \mathbb{R}$ and a scale $b > 0$, the Laplace mechanism releases
$f(x) + Y$ with $Y \sim \mathrm{Lap}(0, b)$, i.e. its output law is the probability measure
$\mathrm{Lap}(f(x), b)$. The
scale is calibrated as $b = \Delta f / \varepsilon$, where $\Delta f$ bounds the change of $f$ between
neighbours. The source defines it for $f : X \to \mathbb{R}^k$ with independent noise on each
coordinate; that form appears in the vector-valued theorem.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/privacybook.html>, Definition 3.1 ($\ell_1$-sensitivity) and Definition 3.3.
- C. Dwork, F. McSherry, K. Nissim and A. Smith, *Calibrating noise to sensitivity in private data analysis*, TCC 2006 (the Laplace mechanism, cited in Dwork and Roth 2014, Section 3.7).
