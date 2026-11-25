# Embedding of IMP into the heap language

The embedding sends each plain IMP command to
the heap command of the same shape: $\mathtt{skip}$ goes to $\mathtt{skip}$, an assignment of an
arithmetic expression to a variable goes to the same assignment, a sequence goes to the
sequence of the embeddings of its parts, and a conditional or while loop goes to the conditional
or while loop with the same guard and with each subcommand replaced by its embedding.
