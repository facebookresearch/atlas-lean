# Erase With Cost time of lookup eq none

For any hash table and key, if the lookup of the key returns nothing and the chain of the key's selected bucket has $n$ entries, the counted erasure of the key costs exactly $n + 1$ scan events: one unsuccessful comparison per entry and the terminal event at the end of the chain. No validity hypothesis on the table is needed.
