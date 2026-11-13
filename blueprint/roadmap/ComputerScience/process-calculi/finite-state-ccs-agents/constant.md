# Constants listing their transitions realize them

Fix a recursive specification, a map
$\iota$ from codes to process constants and a function $s$ listing labelled transitions for
each code. Suppose that for every code $x$, writing $(a_1, y_1), \dots, (a_n, y_n)$ for the
entries of $s(x)$ in order, the body of the constant $\iota(x)$ is
$a_1.\iota(y_1) + (a_2.\iota(y_2) + \dots + (a_n.\iota(y_n) + 0))$, which is $0$ when $n = 0$.
Then the processes $\iota(x)$, indexed by codes $x$, realize $s$.
