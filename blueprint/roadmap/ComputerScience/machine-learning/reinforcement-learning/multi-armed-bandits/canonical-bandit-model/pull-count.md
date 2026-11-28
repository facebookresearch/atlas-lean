# Pull count of an arm

The pull count of arm $i$ in a history $(A_1, X_1, \dots, A_n, X_n)$ of $n$ rounds is
$T_i(n) = \#\{t \le n : A_t = i\}$, the number of rounds in which arm $i$ is chosen. On the canonical bandit model
it is a random variable, as the arms $A_t$ are the coordinates of the history.

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), Section 4.5 (the number $T_a(t)$ of times action $a$ is chosen in the first $t$ rounds). <https://tor-lattimore.com/downloads/book/book.pdf>
