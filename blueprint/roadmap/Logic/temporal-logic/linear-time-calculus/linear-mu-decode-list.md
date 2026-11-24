# Decoding a linear μ-calculus token list to a formula

Decoding of token lists into linear μ-calculus formulas: it parses the whole list as one formula, with one
more unit of fuel than the list has tokens, and returns that formula if no tokens are left over;
otherwise decoding fails. Decoding the tokens of a formula returns that formula, but decoding is
not an exact inverse of the encoding: the parser ignores the second component of the tokens for
$\bot$, $\top$ and the connectives, so lists that are not encodings also decode. For example the
one-token list $[\langle 3, 1\rangle]$ decodes to $\bot$, whose encoding is $[\langle 3, 0\rangle]$.
