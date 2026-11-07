# Labbé's palindromic fixed point outside class P

The conjecture holds: there exist a
primitive morphism $\varphi$ on the alphabet $\{0, 1, 2\}$ (some power $\varphi^n$ maps every letter
to a word containing every letter) and an infinite word $u$ such that $u$ is a fixed point of
$\varphi$, $u$ is palindromic (it has arbitrarily long palindromic factors) and uniformly recurrent
(for every factor $w$ of $u$ there is $B$ such that, for every $k$, $w$ occurs in $u$ starting at
some position in $[k, k + B]$), and no morphism $\psi$ that has $u$ as a fixed point and is not the
identity is conjugate to a morphism $\theta$ in class P. Here $u$ is a fixed point of $\psi$ when,
for some letter $a$, the word $\psi(a)$ begins with $a$, the words $\psi^m(a)$ are arbitrarily
long, and every $\psi^m(a)$ is a prefix of $u$; $\psi$ and $\theta$ are conjugate when there is a
word $w$ with $\psi(a)w = w\theta(a)$ for every letter $a$, or with $\theta(a)w = w\psi(a)$ for
every letter $a$; and $\theta$ is in class P when there is a palindrome $p$ such that each
$\theta(a)$ is $p$ followed by a palindrome.

Over a binary alphabet the question of Hof, Knill and Simon has a positive answer (Tan 2007).

## Sources

- Sébastien Labbé, A counterexample to a question of Hof, Knill and Simon, Electron. J. Combin. 21 (2014) #P3.11, https://doi.org/10.37236/3758. Moved from `OpenConjectures/Combinatorics/PalindromicRecurrentOutsideP`.
