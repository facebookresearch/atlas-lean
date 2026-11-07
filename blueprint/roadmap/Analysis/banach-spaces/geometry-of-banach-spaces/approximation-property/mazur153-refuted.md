# Negative answer to Mazur's Problem 153

There are a continuous function
$f \colon [0,1]^2 \to \mathbb{R}$ and a real number $\varepsilon > 0$ such that for every natural
number $n$, all points $a_1, \dots, a_n, b_1, \dots, b_n \in [0,1]$ and all real numbers
$c_1, \dots, c_n$ there are $x, y \in [0,1]$ with

$$\Bigl| f(x, y) - \sum_{k=1}^n c_k \, f(a_k, y) \, f(x, b_k) \Bigr| > \varepsilon.$$

That is, the approximation scheme of Mazur's Problem 153 fails.

## Sources

- S. Mazur, Problem 153 of the Scottish Book; refuted via P. Enflo's counterexample to the approximation problem in Banach spaces, Acta Math. 130 (1973), 309–317, DOI 10.1007/BF02392270; see the commentary in R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015). This is the original bivariate-function form of the problem, distinct from the approximation-property consequence already in `EnfloWanted.lean`.
