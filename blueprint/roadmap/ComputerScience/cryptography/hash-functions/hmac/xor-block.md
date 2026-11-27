# Bitwise exclusive or of two words

The bitwise exclusive or of two words $x, y$ of the same width $w$ (possibly $w = 0$) is the word whose $i$-th bit is $x_i \oplus y_i$. It has two representations: for length-$w$ bit vectors it applies exclusive or coordinatewise, and for functions $\{0, \dots, w-1\} \to \{0,1\}$ it is $i \mapsto x(i) \oplus y(i)$. The two agree under the correspondence between a vector and its function of indices.
