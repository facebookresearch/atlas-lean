# First-order logic of order over infinite words

Let $\Sigma$ be a finite alphabet. The logic $\mathrm{FO}[<]$ over $\omega$-words has first-order variables ranging over positions $\mathbb{N}$, atomic formulas $x < y$, $x = y$ and $P_a(x)$ for $a \in \Sigma$, and Boolean connectives and first-order quantifiers. For $w = a_0 a_1 \cdots \in \Sigma^\omega$ and an assignment $\beta$ of positions to the free variables, $w, \beta \models P_a(x)$ when $a_{\beta(x)} = a$, $w, \beta \models x < y$ when $\beta(x) < \beta(y)$, and the other clauses are as usual. Viewing $w$ as the chain $(\mathbb{N}, <)$ in which $P_a$ holds at the positions labelled $a$, this is the first-order monadic logic of order over that chain.

## Sources

- J. A. W. Kamp, *Tense Logic and the Theory of Linear Order*, PhD thesis, University of California, Los Angeles, 1968
- A. Rabinovich, "A proof of Kamp's theorem", *Logical Methods in Computer Science* 10(1):14, 2014, Section 2.1, <https://arxiv.org/abs/1401.2580>
- W. Thomas, "Languages, automata, and logic", in G. Rozenberg and A. Salomaa (eds.), *Handbook of Formal Languages*, vol. 3, Springer, 1997
