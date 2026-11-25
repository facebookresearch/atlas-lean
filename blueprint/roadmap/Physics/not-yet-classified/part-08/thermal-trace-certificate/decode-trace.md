# Bounded thermal trace decoder

The decoder takes a character list $s$. If $s$ has at most $300$ characters and splitting $s$ at every comma gives exactly eleven pieces, it decodes each piece as a token and returns the list of the eleven token values when every token decodes; in every other case it returns no value.

A token decodes when splitting it at `/` gives exactly two parts $a$ and $b$, where $a$ is an optional `-` followed by one to eleven decimal digits denoting an integer $z$ with $|z| \le 10^{10}$, and $b$ is one to eleven decimal digits denoting an integer $d$ with $1 \le d \le 10^{10}$. The value of the token is the rational $z/d$.
