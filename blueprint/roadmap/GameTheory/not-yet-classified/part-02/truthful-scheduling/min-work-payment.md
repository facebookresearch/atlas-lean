# MinWork payment

For finitely many machines (at least two) and finitely many tasks with processing times $t_k(j)$, MinWork assigns each task to a fastest machine and pays machine $i$, for each task $j$ assigned to it, the fastest processing time among the other machines: the payment is $\sum_{j \text{ won by } i} \min_{k \ne i} t_k(j)$.
