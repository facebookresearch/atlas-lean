# Smith normal form

Let $R$ be a principal ideal domain, let $M$ be a finitely generated free
$R$-module and let $N$ be a submodule of $M$. Then there are natural numbers $n \le m$, a basis
$e_0, \dots, e_{m-1}$ of $M$, a basis $f_0, \dots, f_{n-1}$ of $N$ and nonzero elements
$a_0, \dots, a_{n-1}$ of $R$ such that $f_i = a_i e_i$ in $M$ for every $i < n$ and
$a_i \mid a_{i+1}$ whenever $i + 1 < n$.

## Sources

- H. J. S. Smith, Phil. Trans. R. Soc. Lond. 151 (1861), 293-326, DOI 10.1098/RSTL.1861.0016. It is `Submodule.exists_smith_normal_form_dvd_chain`, kept under the source's name. Proves `Wanted` entry `smithNormalForm`.
