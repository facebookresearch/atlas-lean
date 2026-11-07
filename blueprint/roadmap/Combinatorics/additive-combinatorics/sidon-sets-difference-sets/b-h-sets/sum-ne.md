# Sum of a nonempty list

For a nonempty list $(a_1, \dots, a_k)$ of elements of a type with
an addition, its sum is obtained by adding the entries from left to right starting from the head:
it is $a_1$ when $k = 1$, and $(\cdots((a_1 + a_2) + a_3) + \cdots) + a_k$ in general. No zero
element is needed, and the proof that the list is nonempty does not affect the value.
