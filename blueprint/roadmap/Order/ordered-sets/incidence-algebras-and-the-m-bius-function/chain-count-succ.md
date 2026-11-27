# Removing the last step of a chain

Removing the top element of a chain of length $i + 1$ ending at $b$ leaves a chain of length $i$
ending at some $x < b$, and this is a bijection:

$$c_{i+1}(a, b) = \sum_{a \le x < b} c_i(a, x).$$
