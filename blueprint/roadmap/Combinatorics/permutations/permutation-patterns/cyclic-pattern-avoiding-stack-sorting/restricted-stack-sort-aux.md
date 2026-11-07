# Restricted stack-sorting from a given stack

Fix a property of finite sequences of natural
numbers, called bad. Given an input sequence $\pi$ and a stack (listed from top to bottom), read
$\pi$ from left to right. Before pushing the next entry $x$, pop the least number $k$ of entries
from the top of the stack such that the remaining stack with $x$ pushed on top, read from top to
bottom, is not bad (if there is no such $k$, the whole stack is popped and $x$ is pushed anyway);
popped entries are appended to the output in the order they are removed. When the input is
exhausted, the remaining stack is appended to the output from top to bottom. The map returns this
output.

## Sources

- Alex Zhan and Stella Bie, *Cyclic-Pattern-Avoiding Stacks*, INTEGERS 26 (2026), Article A15, Section 1 (Berlow's map `s_T`).
