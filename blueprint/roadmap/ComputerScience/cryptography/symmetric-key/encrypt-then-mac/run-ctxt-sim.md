# The simulation runs the ciphertext forger exactly

Against the MAC oracle $F(k_2, \cdot)$, the simulation of a ciphertext forger on a tape has the same
output as the forger run on the same tape against encrypt-then-MAC encryption under $(k_1, k_2)$; the
values it asks to be tagged are the first components of the forger's answers; and every answer
$(c, t)$ in the forger's transcript has $t = F(k_2, c)$.
