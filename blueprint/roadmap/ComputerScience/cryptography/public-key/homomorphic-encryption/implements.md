# Implements

The bit circuit computes decryption on every secret key and ciphertext in the declared
spaces. Its input holds the framed key followed by the framed ciphertext; its output holds the
framed result (empty for rejection, a one followed by the message for success). Both sides must
fit their ports before zero padding. A frame prefixes each data bit by a one and ends in zero.
