# State of the simulated chosen-ciphertext game

The simulation of the chosen-ciphertext game keeps three things: the table of the encryption answers
given so far, each with its message; a query counter; and the index of the first bad query, if any,
where a bad query is a decryption query on a fresh ciphertext with a valid tag.
