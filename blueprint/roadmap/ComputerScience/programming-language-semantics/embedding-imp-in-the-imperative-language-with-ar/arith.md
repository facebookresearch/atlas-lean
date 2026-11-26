# Translating IMP arithmetic expressions into the imperative language with arrays

For a renaming $\rho$ from natural numbers to strings, the translation $\tau_\rho(a)$ of an IMP arithmetic expression $a$ is defined by recursion on $a$: the constant $n$ goes to the numeral $n$, the variable $x_i$ goes to the variable $\rho(i)$, and $a_1 + a_2$, $a_1 - a_2$ and $a_1 \cdot a_2$ go to $\tau_\rho(a_1) + \tau_\rho(a_2)$, $\tau_\rho(a_1) - \tau_\rho(a_2)$ and $\tau_\rho(a_1) \cdot \tau_\rho(a_2)$.
